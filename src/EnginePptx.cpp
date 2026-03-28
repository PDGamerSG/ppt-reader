/* Copyright 2022 the SumatraPDF project authors (see AUTHORS file).
   License: GPLv3 */

#include "utils/BaseUtil.h"
#include "utils/Archive.h"
#include "utils/ScopedWin.h"
#include "utils/FileUtil.h"
#include "utils/GuessFileType.h"
#include "utils/GdiPlusUtil.h"
#include "utils/HtmlParserLookup.h"
#include "utils/HtmlPullParser.h"
#include "utils/WinUtil.h"
#include "utils/Dpi.h"

#include "wingui/UIModels.h"

#include "DocProperties.h"
#include "DocController.h"
#include "EngineBase.h"
#include "EngineAll.h"
#include "EnginePptx.h"

#include "utils/Log.h"

using Gdiplus::Bitmap;
using Gdiplus::Color;
using Gdiplus::Font;
using Gdiplus::FontStyleBold;
using Gdiplus::FontStyleItalic;
using Gdiplus::FontStyleRegular;
using Gdiplus::FontStyleStrikeout;
using Gdiplus::FontStyleUnderline;
using Gdiplus::Graphics;
using Gdiplus::GraphicsPath;
using Gdiplus::InterpolationModeHighQualityBicubic;
using Gdiplus::Matrix;
using Gdiplus::MatrixOrderAppend;
using Gdiplus::Ok;
using Gdiplus::Pen;
using Gdiplus::SmoothingModeAntiAlias;
using Gdiplus::SolidBrush;
using Gdiplus::Status;
using Gdiplus::StringAlignment;
using Gdiplus::StringAlignmentCenter;
using Gdiplus::StringAlignmentFar;
using Gdiplus::StringAlignmentNear;
using Gdiplus::StringFormat;
using Gdiplus::UnitPixel;
using Gdiplus::UnitPoint;

Kind kindEnginePptx = "enginePptx";

// EMU (English Metric Units): 914400 EMU = 1 inch = 96 px at 96 DPI
static const float kEmuPerInch = 914400.0f;
static const float kRenderDpi = 96.0f;

static float EmuToPx(i64 emu, float zoom) {
    return (float)emu / kEmuPerInch * kRenderDpi * zoom;
}

// Convert font size in points to pixels at our reference 96 DPI.
// We use UnitPixel for fonts (not UnitPoint) because UnitPoint uses the
// system DPI which may differ from our coordinate system's 96 DPI,
// causing fonts to appear too large on high-DPI displays.
static float PtToPx(float pt) {
    return pt * (kRenderDpi / 72.0f);
}

// parse a 6-hex-digit color string "RRGGBB" -> COLORREF
static COLORREF ParseHexColor(const char* s, size_t len) {
    if (len < 6) {
        return RGB(0, 0, 0);
    }
    char buf[7];
    memcpy(buf, s, 6);
    buf[6] = '\0';
    unsigned long v = strtoul(buf, nullptr, 16);
    return RGB((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF);
}

static i64 ParseAttrI64(AttrInfo* a) {
    if (!a || a->valLen == 0) {
        return 0;
    }
    char buf[32];
    size_t n = a->valLen < sizeof(buf) - 1 ? a->valLen : sizeof(buf) - 1;
    memcpy(buf, a->val, n);
    buf[n] = '\0';
    return (i64)_atoi64(buf);
}

static float ParseAttrFloat(AttrInfo* a) {
    if (!a || a->valLen == 0) {
        return 0.0f;
    }
    char buf[32];
    size_t n = a->valLen < sizeof(buf) - 1 ? a->valLen : sizeof(buf) - 1;
    memcpy(buf, a->val, n);
    buf[n] = '\0';
    return (float)atof(buf);
}

static bool ParseAttrBool(AttrInfo* a) {
    if (!a || a->valLen == 0) {
        return false;
    }
    // OOXML: "1" or "true"; also bare attribute with no value means true
    if (a->valLen == a->nameLen && a->val == a->name) {
        return true; // value-less attribute
    }
    return a->val[0] == '1' || (a->valLen >= 4 && a->val[0] == 't');
}

static bool TagIs(HtmlToken* tok, const char* localName) {
    return tok->NameIsNS(localName, nullptr);
}

// Apply tint (0-100000) to a color component: tint blends toward white
static BYTE ApplyTint(BYTE c, int tintVal) {
    // tintVal: 0 = black, 100000 = original
    float t = (float)tintVal / 100000.0f;
    return (BYTE)(c * t + 255.0f * (1.0f - t));
}

// Apply shade (0-100000) to a color component: shade blends toward black
static BYTE ApplyShade(BYTE c, int shadeVal) {
    float s = (float)shadeVal / 100000.0f;
    return (BYTE)(c * s);
}

// Apply lumMod + lumOff (both in 100000ths)
static BYTE ApplyLumMod(BYTE c, int lumMod, int lumOff) {
    float v = (float)c / 255.0f;
    v = v * (lumMod / 100000.0f) + (lumOff / 100000.0f);
    if (v < 0.0f) {
        v = 0.0f;
    }
    if (v > 1.0f) {
        v = 1.0f;
    }
    return (BYTE)(v * 255.0f);
}

// ===== Data Structures =====

// Theme color scheme (from ppt/theme/theme1.xml)
struct PptxTheme {
    COLORREF dk1 = RGB(0, 0, 0);
    COLORREF lt1 = RGB(255, 255, 255);
    COLORREF dk2 = RGB(68, 84, 106);
    COLORREF lt2 = RGB(231, 230, 230);
    COLORREF accent1 = RGB(68, 114, 196);
    COLORREF accent2 = RGB(237, 125, 49);
    COLORREF accent3 = RGB(165, 165, 165);
    COLORREF accent4 = RGB(255, 192, 0);
    COLORREF accent5 = RGB(91, 155, 213);
    COLORREF accent6 = RGB(112, 173, 71);
    COLORREF hlink = RGB(5, 99, 193);
    COLORREF folHlink = RGB(149, 79, 114);
    char* minorFont = nullptr; // body font (Calibri, etc.)
    char* majorFont = nullptr; // heading font

    ~PptxTheme() {
        str::Free(minorFont);
        str::Free(majorFont);
    }

    COLORREF GetSchemeColor(const char* val, size_t len) const {
        if (str::EqNI(val, "dk1", len) || str::EqNI(val, "tx1", len)) {
            return dk1;
        }
        if (str::EqNI(val, "lt1", len) || str::EqNI(val, "bg1", len)) {
            return lt1;
        }
        if (str::EqNI(val, "dk2", len) || str::EqNI(val, "tx2", len)) {
            return dk2;
        }
        if (str::EqNI(val, "lt2", len) || str::EqNI(val, "bg2", len)) {
            return lt2;
        }
        if (str::EqNI(val, "accent1", len)) {
            return accent1;
        }
        if (str::EqNI(val, "accent2", len)) {
            return accent2;
        }
        if (str::EqNI(val, "accent3", len)) {
            return accent3;
        }
        if (str::EqNI(val, "accent4", len)) {
            return accent4;
        }
        if (str::EqNI(val, "accent5", len)) {
            return accent5;
        }
        if (str::EqNI(val, "accent6", len)) {
            return accent6;
        }
        if (str::EqNI(val, "hlink", len)) {
            return hlink;
        }
        if (str::EqNI(val, "folHlink", len)) {
            return folHlink;
        }
        return RGB(0, 0, 0);
    }
};

// Per-level text style (from slide master <p:txStyles>)
struct PptxLevelStyle {
    float fontSize = 0.0f;
    COLORREF color = (COLORREF)-1;
    bool bold = false;
    bool italic = false;
    char* fontName = nullptr;
    i64 marL = -1;
    i64 indent = 0;
    bool hasBullet = false;
    bool bulletIsNone = false;
    char* bulletChar = nullptr;
    char* bulletFont = nullptr;
    COLORREF bulletColor = (COLORREF)-1;
    float bulletSzPct = 0.0f; // bullet size as % of text (0=same)

    ~PptxLevelStyle() {
        str::Free(fontName);
        str::Free(bulletChar);
        str::Free(bulletFont);
    }
};

// Text styles from slide master (<p:txStyles>)
struct PptxTxStyles {
    PptxLevelStyle titleLevels[9]; // from <p:titleStyle>
    PptxLevelStyle bodyLevels[9];  // from <p:bodyStyle>
    PptxLevelStyle otherLevels[9]; // from <p:otherStyle>

    const PptxLevelStyle* GetLevel(const char* phType, int lvl) const {
        if (lvl < 0) {
            lvl = 0;
        }
        if (lvl > 8) {
            lvl = 8;
        }
        if (phType) {
            if (str::EqI(phType, "title") || str::EqI(phType, "ctrTitle")) {
                return &titleLevels[lvl];
            }
            if (str::EqI(phType, "subTitle") || str::EqI(phType, "body") || str::EqI(phType, "obj") ||
                str::EqI(phType, "clipArt") || str::EqI(phType, "tbl") || str::EqI(phType, "chart") ||
                str::EqI(phType, "dgm") || str::EqI(phType, "media")) {
                return &bodyLevels[lvl];
            }
        }
        return &otherLevels[lvl];
    }
};

// Paragraph-level properties
struct PptxParaProps {
    int algn = -1;          // -1=inherit, 0=left, 1=center, 2=right, 3=justify
    i64 marL = -1;          // left margin EMU (-1=inherit)
    i64 indent = 0;         // first-line indent EMU (negative=hanging)
    int lvl = 0;            // outline level 0-8
    float lnSpcPct = 0.0f;  // line spacing % (0=inherit/100%)
    float lnSpcPts = 0.0f;  // line spacing absolute in points (0=use pct)
    float spcBefPt = 0.0f;  // space before in points
    float spcAftPt = 0.0f;  // space after in points
    float spcBefPct = 0.0f; // space before as % of line (0=use pt)
    float spcAftPct = 0.0f; // space after as % of line (0=use pt)
    // bullet
    bool hasBullet = false;
    bool bulletIsNone = false;
    char bulletChar = 0;           // unicode char as utf-8 first byte for simple ASCII
    char* bulletCharStr = nullptr; // full utf-8 bullet char string
    bool bulletAutoNum = false;
    int bulletAutoNumStart = 1;
    char* buFontName = nullptr;      // <a:buFont typeface="...">
    COLORREF buColor = (COLORREF)-1; // <a:buClr>
    float buSzPct = 0.0f;            // <a:buSzPct> bullet size as % of text (0=same)
    float buSzPts = 0.0f;            // <a:buSzPts> bullet size in points (0=use pct)
    // default run properties for runs inside this paragraph
    float defFontSize = 0.0f;
    COLORREF defColor = (COLORREF)-1;
    char* defFont = nullptr;
    bool defBold = false;
    bool defItalic = false;

    PptxParaProps() = default;
    ~PptxParaProps() {
        str::Free(bulletCharStr);
        str::Free(buFontName);
        str::Free(defFont);
    }
};

// Text body properties
struct PptxBodyProps {
    i64 lIns = 91440; // left inset EMU (default ~0.1")
    i64 tIns = 45720; // top inset EMU
    i64 rIns = 91440; // right inset EMU
    i64 bIns = 45720; // bottom inset EMU
    int anchor = 0;   // 0=top, 1=center, 2=bottom
    bool wrap = true;
    bool vert = false;           // vertical text
    float fontScale = 0.0f;      // normAutofit fontScale (0=no scaling, else % like 80.0)
    float lnSpcReduction = 0.0f; // normAutofit lnSpcReduction (0=none, else % like 20.0)
};

struct PptxTextRun {
    char* text = nullptr;
    float fontSize = 0.0f; // 0 = inherit from para default
    bool bold = false;
    bool italic = false;
    bool underline = false;
    bool strikethrough = false;
    COLORREF color = (COLORREF)-1; // -1 = inherit
    char* fontName = nullptr;      // nullptr = use theme minor font
    int spc = INT_MIN;             // character spacing in hundredths of a point (INT_MIN = not set)

    ~PptxTextRun() {
        str::Free(text);
        str::Free(fontName);
    }
};

struct PptxPara {
    Vec<PptxTextRun*> runs;
    PptxParaProps props;

    ~PptxPara() { DeleteVecMembers(runs); }
};

struct PptxPathPt {
    i64 x = 0, y = 0;
};

enum class PptxPathCmdType {
    MoveTo,
    LineTo,
    Close
};

struct PptxPathCmd {
    PptxPathCmdType type = PptxPathCmdType::MoveTo;
    PptxPathPt pt;
};

struct PptxCustPath {
    i64 w = 0, h = 0; // path coordinate space (0 = use shape extCx/extCy)
    Vec<PptxPathCmd> cmds;
};

enum class PptxShapeType {
    Text,
    Image,
    Connector
};

struct PptxShape {
    PptxShapeType type = PptxShapeType::Text;
    i64 offX = 0, offY = 0, extCx = 0, extCy = 0;
    int rot = 0; // 1/60000 degrees clockwise
    bool flipH = false, flipV = false;
    COLORREF fillColor = (COLORREF)-1;
    COLORREF borderColor = (COLORREF)-1; // -1 = use theme dk1 if borderWidth>0
    float borderWidth = 0.0f;            // in EMU (0 = no border)
    bool noBorder = false;               // explicit <a:noFill/> in <a:ln>
    Vec<PptxPara*> paras;
    char* imagePath = nullptr;
    PptxBodyProps bodyProps;
    // Placeholder tracking
    int phIdx = -1;               // <p:ph idx="N"> (-1 = not a placeholder)
    char* phType = nullptr;       // <p:ph type="title"|"body"|...> (nullptr = none)
    bool hasExplicitXfrm = false; // true if <a:xfrm> was present in spPr
    float phDefFontSize = 0.0f;   // default font size inherited from layout/master
    bool phDefBold = false;       // default bold inherited from layout/master
    Vec<PptxCustPath*> custPaths; // from <a:custGeom>
    char* prstGeom = nullptr;     // preset geometry name ("roundRect", "ellipse", etc.)

    ~PptxShape() {
        DeleteVecMembers(paras);
        str::Free(imagePath);
        str::Free(phType);
        str::Free(prstGeom);
        DeleteVecMembers(custPaths);
    }
};

struct PptxSlide {
    Vec<PptxShape*> shapes;
    COLORREF bgColor = (COLORREF)-1; // -1 = use theme/white
    char* bgImagePath = nullptr;     // ZIP path for blipFill slide background

    ~PptxSlide() {
        DeleteVecMembers(shapes);
        str::Free(bgImagePath);
    }
};

struct PptxDoc {
    MultiFormatArchive* archive = nullptr;
    char* filePath = nullptr;
    i64 slideCx = 9144000;
    i64 slideCy = 6858000;
    Vec<char*> slidePaths;
    Vec<PptxSlide*> slides;
    Props props;
    PptxTheme* theme = nullptr;
    PptxTxStyles* txStyles = nullptr; // from slide master <p:txStyles>

    ~PptxDoc() {
        delete archive;
        str::Free(filePath);
        for (char* p : slidePaths) {
            str::Free(p);
        }
        DeleteVecMembers(slides);
        delete theme;
        delete txStyles;
    }
};

// ===== Group Shape Transform =====

struct GroupTransform {
    i64 offX = 0, offY = 0;       // group position in parent coords (EMU)
    i64 extCx = 0, extCy = 0;     // group size in parent coords (EMU)
    i64 chOffX = 0, chOffY = 0;   // child coord origin
    i64 chExtCx = 0, chExtCy = 0; // child coord extent
    bool valid = false;
};

// Apply one group-level coordinate transform to a child shape's geometry.
// Converts (x,y,cx,cy) from the group's child-coordinate space to parent space.
static void ApplyGroupTransform(const GroupTransform& grp, i64& x, i64& y, i64& cx, i64& cy) {
    if (!grp.valid || grp.chExtCx == 0 || grp.chExtCy == 0) {
        return;
    }
    double sx = (double)grp.extCx / (double)grp.chExtCx;
    double sy = (double)grp.extCy / (double)grp.chExtCy;
    x = grp.offX + (i64)((double)(x - grp.chOffX) * sx);
    y = grp.offY + (i64)((double)(y - grp.chOffY) * sy);
    cx = (i64)((double)cx * sx);
    cy = (i64)((double)cy * sy);
}

// ===== Placeholder Position Table =====

struct PlaceholderPos {
    int idx = -1;           // ph idx (-1 = not set)
    char* phType = nullptr; // ph type ("title", "body", etc.) or nullptr
    i64 offX = 0, offY = 0, extCx = 0, extCy = 0;
    bool hasPos = false;
    float defFontSize = 0.0f; // from lstStyle defRPr sz= (in points)
    bool defBold = false;     // from lstStyle defRPr b=

    ~PlaceholderPos() { str::Free(phType); }
};

// Parse a layout or master XML and collect placeholder positions and default text formatting.
// Records <p:sp> with <p:ph> that has <a:xfrm>; also extracts defRPr font size from lstStyle.
static void ExtractPlaceholderPositions(MultiFormatArchive* archive, const char* xmlPath, Vec<PlaceholderPos*>& out) {
    ByteSlice data = archive->GetFileDataByName(xmlPath);
    if (!data) {
        return;
    }
    HtmlPullParser parser(data);
    HtmlToken* tok;
    PlaceholderPos* cur = nullptr;
    bool inSpPr = false;
    bool inXfrm = false;
    bool inSp = false;
    bool inTxBody = false;
    bool inLstStyle = false;
    bool inLvl1pPr = false;

    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag()) {
            if (TagIs(tok, "sp")) {
                if (cur && cur->hasPos) {
                    out.Append(cur);
                } else {
                    delete cur;
                }
                cur = nullptr;
                inSp = false;
                inSpPr = false;
                inXfrm = false;
                inTxBody = false;
                inLstStyle = false;
                inLvl1pPr = false;
            } else if (TagIs(tok, "spPr")) {
                inSpPr = false;
            } else if (TagIs(tok, "xfrm")) {
                inXfrm = false;
            } else if (TagIs(tok, "txBody")) {
                inTxBody = false;
                inLstStyle = false;
                inLvl1pPr = false;
            } else if (TagIs(tok, "lstStyle")) {
                inLstStyle = false;
                inLvl1pPr = false;
            } else if (TagIs(tok, "lvl1pPr")) {
                inLvl1pPr = false;
            }
            continue;
        }
        if (!tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
            continue;
        }
        if (TagIs(tok, "sp")) {
            inSp = true;
            cur = new PlaceholderPos();
        } else if (inSp && TagIs(tok, "ph")) {
            if (cur) {
                AttrInfo* idx = tok->GetAttrByName("idx");
                if (idx) {
                    cur->idx = (int)ParseAttrI64(idx);
                }
                AttrInfo* type = tok->GetAttrByName("type");
                if (type && type->valLen > 0) {
                    str::Free(cur->phType);
                    cur->phType = str::Dup(type->val, type->valLen);
                }
            }
        } else if (inSp && TagIs(tok, "spPr")) {
            inSpPr = true;
        } else if (inSp && inSpPr && TagIs(tok, "xfrm")) {
            inXfrm = true;
        } else if (inSp && inXfrm && TagIs(tok, "off")) {
            if (cur) {
                cur->offX = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
                cur->offY = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
            }
        } else if (inSp && inXfrm && TagIs(tok, "ext")) {
            if (cur) {
                cur->extCx = ParseAttrI64(tok->GetAttrByNameNS("cx", nullptr));
                cur->extCy = ParseAttrI64(tok->GetAttrByNameNS("cy", nullptr));
                if (cur->extCx > 0 && cur->extCy > 0) {
                    cur->hasPos = true;
                }
            }
        } else if (inSp && TagIs(tok, "txBody")) {
            inTxBody = true;
        } else if (inSp && inTxBody && TagIs(tok, "lstStyle")) {
            inLstStyle = true;
        } else if (inSp && inLstStyle && TagIs(tok, "lvl1pPr")) {
            inLvl1pPr = true;
        } else if (inSp && inLvl1pPr && TagIs(tok, "defRPr")) {
            if (cur) {
                AttrInfo* sz = tok->GetAttrByName("sz");
                if (sz && sz->valLen > 0 && cur->defFontSize == 0.0f) {
                    cur->defFontSize = ParseAttrFloat(sz) / 100.0f;
                }
                AttrInfo* b = tok->GetAttrByName("b");
                if (b && ParseAttrBool(b)) {
                    cur->defBold = true;
                }
            }
        }
    }
    delete cur; // any unclosed sp
    data.Free();
}

// Look up a placeholder position by idx first, then by type name.
static const PlaceholderPos* LookupPhPos(const Vec<PlaceholderPos*>& table, int idx, const char* phType) {
    // First try exact idx match
    if (idx >= 0) {
        for (PlaceholderPos* p : table) {
            if (p->idx == idx && p->hasPos) {
                return p;
            }
        }
    }
    // Then try type match
    if (phType) {
        for (PlaceholderPos* p : table) {
            if (p->phType && str::EqI(p->phType, phType) && p->hasPos) {
                return p;
            }
        }
    }
    // Fallback: if this is body (idx=1) and we didn't find idx=1, try type "body"
    if (idx == 1 && !phType) {
        for (PlaceholderPos* p : table) {
            if (p->phType && str::EqI(p->phType, "body") && p->hasPos) {
                return p;
            }
        }
    }
    return nullptr;
}

// ===== Theme Parser =====

static void ParseTheme(PptxDoc* doc, const char* themePath) {
    ByteSlice data = doc->archive->GetFileDataByName(themePath);
    if (!data) {
        return;
    }
    auto* theme = new PptxTheme();

    // Current color slot being filled
    COLORREF* curSlot = nullptr;
    bool inFontScheme = false;
    bool inMajorFont = false;
    bool inMinorFont = false;

    HtmlPullParser parser(data);
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag()) {
            if (TagIs(tok, "clrScheme")) {
                curSlot = nullptr;
            }
            if (TagIs(tok, "fontScheme")) {
                inFontScheme = false;
                inMajorFont = false;
                inMinorFont = false;
            }
            if (TagIs(tok, "majorFont")) {
                inMajorFont = false;
            }
            if (TagIs(tok, "minorFont")) {
                inMinorFont = false;
            }
            continue;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }

        // Color scheme slots
        if (TagIs(tok, "dk1")) {
            curSlot = &theme->dk1;
        } else if (TagIs(tok, "lt1")) {
            curSlot = &theme->lt1;
        } else if (TagIs(tok, "dk2")) {
            curSlot = &theme->dk2;
        } else if (TagIs(tok, "lt2")) {
            curSlot = &theme->lt2;
        } else if (TagIs(tok, "accent1")) {
            curSlot = &theme->accent1;
        } else if (TagIs(tok, "accent2")) {
            curSlot = &theme->accent2;
        } else if (TagIs(tok, "accent3")) {
            curSlot = &theme->accent3;
        } else if (TagIs(tok, "accent4")) {
            curSlot = &theme->accent4;
        } else if (TagIs(tok, "accent5")) {
            curSlot = &theme->accent5;
        } else if (TagIs(tok, "accent6")) {
            curSlot = &theme->accent6;
        } else if (TagIs(tok, "hlink")) {
            curSlot = &theme->hlink;
        } else if (TagIs(tok, "folHlink")) {
            curSlot = &theme->folHlink;
        } else if (TagIs(tok, "fontScheme")) {
            inFontScheme = true;
        } else if (inFontScheme && TagIs(tok, "majorFont")) {
            inMajorFont = true;
            inMinorFont = false;
        } else if (inFontScheme && TagIs(tok, "minorFont")) {
            inMinorFont = true;
            inMajorFont = false;
        } else if (curSlot && TagIs(tok, "srgbClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                *curSlot = ParseHexColor(v->val, v->valLen);
            }
            curSlot = nullptr;
        } else if (curSlot && TagIs(tok, "sysClr")) {
            // use lastClr fallback
            AttrInfo* lc = tok->GetAttrByName("lastClr");
            if (lc) {
                *curSlot = ParseHexColor(lc->val, lc->valLen);
            }
            curSlot = nullptr;
        } else if (inFontScheme && TagIs(tok, "latin")) {
            AttrInfo* tf = tok->GetAttrByName("typeface");
            if (tf && tf->valLen > 0) {
                if (inMajorFont && !theme->majorFont) {
                    theme->majorFont = str::Dup(tf->val, tf->valLen);
                } else if (inMinorFont && !theme->minorFont) {
                    theme->minorFont = str::Dup(tf->val, tf->valLen);
                }
            }
        }
    }
    data.Free();
    doc->theme = theme;
}

// ===== Color Parsing with Theme Resolution =====

// Parse a color element block starting at the current token.
// Supports srgbClr, schemeClr (with tint/shade/lumMod/lumOff transforms).
// Returns (COLORREF)-1 if no color found.
struct ColorParseCtx {
    COLORREF color = (COLORREF)-1;
    bool inSchemeClr = false;
    bool inSrgbClr = false;
    int tint = -1;
    int shade = -1;
    int lumMod = -1;
    int lumOff = 0;
};

static COLORREF ResolveColorCtx(ColorParseCtx& ctx) {
    COLORREF c = ctx.color;
    if (c == (COLORREF)-1) {
        return c;
    }
    BYTE r = GetRValue(c), g = GetGValue(c), b = GetBValue(c);
    if (ctx.lumMod != -1) {
        r = ApplyLumMod(r, ctx.lumMod, ctx.lumOff);
        g = ApplyLumMod(g, ctx.lumMod, ctx.lumOff);
        b = ApplyLumMod(b, ctx.lumMod, ctx.lumOff);
    }
    if (ctx.tint != -1) {
        r = ApplyTint(r, ctx.tint);
        g = ApplyTint(g, ctx.tint);
        b = ApplyTint(b, ctx.tint);
    }
    if (ctx.shade != -1) {
        r = ApplyShade(r, ctx.shade);
        g = ApplyShade(g, ctx.shade);
        b = ApplyShade(b, ctx.shade);
    }
    return RGB(r, g, b);
}

// ===== Relationship File Parser =====

static void ParseRels(MultiFormatArchive* archive, const char* relsPath, Vec<char*>& outRIds, Vec<char*>& outPaths) {
    ByteSlice data = archive->GetFileDataByName(relsPath);
    if (!data) {
        return;
    }
    HtmlPullParser parser(data);
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (!tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
            continue;
        }
        if (!TagIs(tok, "Relationship")) {
            continue;
        }
        AttrInfo* id = tok->GetAttrByName("Id");
        if (!id) {
            continue;
        }
        AutoFreeStr idStr(str::Dup(id->val, id->valLen));
        AttrInfo* target = tok->GetAttrByName("Target");
        if (!target) {
            continue;
        }
        outRIds.Append(idStr.StealData());
        outPaths.Append(str::Dup(target->val, target->valLen));
    }
    data.Free();
}

static void ParseSlideRels(MultiFormatArchive* archive, const char* slideZipPath, Vec<char*>& outRIds,
                           Vec<char*>& outPaths) {
    const char* lastSlash = str::FindCharLast(slideZipPath, '/');
    if (!lastSlash) {
        return;
    }
    AutoFreeStr dirPart(str::Dup(slideZipPath, (size_t)(lastSlash - slideZipPath + 1)));
    const char* fileName = lastSlash + 1;
    AutoFreeStr relsPath(str::Format("%s_rels/%s.rels", dirPart.data, fileName));
    ParseRels(archive, relsPath.data, outRIds, outPaths);

    for (int i = 0; i < outPaths.Size(); i++) {
        char* t = outPaths[i];
        if (str::StartsWith(t, "../")) {
            AutoFreeStr resolved(str::Format("ppt/%s", t + 3));
            str::Free(t);
            outPaths[i] = resolved.StealData();
        } else if (t[0] != '/') {
            AutoFreeStr resolved(str::Format("%s%s", dirPart.data, t));
            str::Free(t);
            outPaths[i] = resolved.StealData();
        }
    }
}

// Look up an rId in parallel arrays and return its path (or nullptr)
static const char* LookupRId(const Vec<char*>& rIds, const Vec<char*>& paths, const char* rId) {
    for (int i = 0; i < rIds.Size(); i++) {
        if (str::Eq(rIds[i], rId)) {
            return paths[i];
        }
    }
    return nullptr;
}

// ===== Color block parser helper =====
// Parses schemeClr / srgbClr / sysClr inside a solidFill or rPr block.
// Caller must have already seen the solidFill start tag.
// Reads tokens until it sees the matching end tag for the parent (solidFill/gradFill).
// Returns the resolved color or (COLORREF)-1.
static COLORREF ParseColorBlock(HtmlPullParser& parser, const PptxTheme* theme) {
    ColorParseCtx ctx;
    const char* schemeVal = nullptr;
    size_t schemeValLen = 0;
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag()) {
            if (TagIs(tok, "solidFill") || TagIs(tok, "srgbClr") || TagIs(tok, "schemeClr") || TagIs(tok, "sysClr")) {
                break;
            }
            continue;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }
        if (TagIs(tok, "srgbClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                ctx.color = ParseHexColor(v->val, v->valLen);
            }
            ctx.inSrgbClr = true;
        } else if (TagIs(tok, "schemeClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v && theme) {
                ctx.color = theme->GetSchemeColor(v->val, v->valLen);
                schemeVal = v->val;
                schemeValLen = v->valLen;
            }
            ctx.inSchemeClr = true;
        } else if (TagIs(tok, "sysClr")) {
            AttrInfo* lc = tok->GetAttrByName("lastClr");
            if (lc) {
                ctx.color = ParseHexColor(lc->val, lc->valLen);
            }
        } else if (TagIs(tok, "tint")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.tint = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "shade")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.shade = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "lumMod")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.lumMod = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "lumOff")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.lumOff = (int)ParseAttrI64(v);
        }
    }
    return ResolveColorCtx(ctx);
}

// Parse color inside a named parent element (e.g. <a:buClr>, <a:bgClr>).
// Reads tokens until the matching end tag for parentEndTag.
static COLORREF ParseColorElement(HtmlPullParser& parser, const char* parentEndTag, const PptxTheme* theme) {
    ColorParseCtx ctx;
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag() && TagIs(tok, parentEndTag)) {
            break;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }
        if (TagIs(tok, "srgbClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                ctx.color = ParseHexColor(v->val, v->valLen);
            }
            ctx.inSrgbClr = true;
        } else if (TagIs(tok, "schemeClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v && theme) {
                ctx.color = theme->GetSchemeColor(v->val, v->valLen);
            }
            ctx.inSchemeClr = true;
        } else if (TagIs(tok, "sysClr")) {
            AttrInfo* lc = tok->GetAttrByName("lastClr");
            if (lc) {
                ctx.color = ParseHexColor(lc->val, lc->valLen);
            }
        } else if (TagIs(tok, "tint")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.tint = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "shade")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.shade = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "lumMod")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.lumMod = (int)ParseAttrI64(v);
        } else if (TagIs(tok, "lumOff")) {
            AttrInfo* v = tok->GetAttrByName("val");
            ctx.lumOff = (int)ParseAttrI64(v);
        }
    }
    return ResolveColorCtx(ctx);
}

// Parse one txStyle section (titleStyle/bodyStyle/otherStyle) into level array.
// Expects parser positioned just after the opening tag (e.g. <p:titleStyle>).
static void ParseTxStyleLevels(HtmlPullParser& parser, const char* endTag, PptxLevelStyle* levels,
                               const PptxTheme* theme) {
    HtmlToken* tok;
    int curLevel = -1;
    bool inDefRPr = false;

    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag()) {
            if (TagIs(tok, endTag)) {
                break;
            }
            if (TagIs(tok, "defRPr")) {
                inDefRPr = false;
            }
            // Check for lvlNpPr end
            if (curLevel >= 0) {
                char buf[16];
                str::BufFmt(buf, sizeof(buf), "lvl%dpPr", curLevel + 1);
                if (TagIs(tok, buf)) {
                    curLevel = -1;
                    inDefRPr = false;
                }
            }
            continue;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }
        // Match lvl1pPr through lvl9pPr
        bool matched = false;
        for (int i = 0; i < 9 && !matched; i++) {
            char buf[16];
            str::BufFmt(buf, sizeof(buf), "lvl%dpPr", i + 1);
            if (TagIs(tok, buf)) {
                curLevel = i;
                matched = true;
                AttrInfo* marL = tok->GetAttrByName("marL");
                if (marL) {
                    levels[i].marL = ParseAttrI64(marL);
                }
                AttrInfo* indent = tok->GetAttrByName("indent");
                if (indent) {
                    levels[i].indent = ParseAttrI64(indent);
                }
            }
        }
        if (matched) {
            continue;
        }

        if (curLevel < 0) {
            continue;
        }
        PptxLevelStyle& ls = levels[curLevel];

        if (TagIs(tok, "buFont")) {
            AttrInfo* tf = tok->GetAttrByName("typeface");
            if (tf && tf->valLen > 0) {
                str::Free(ls.bulletFont);
                ls.bulletFont = str::Dup(tf->val, tf->valLen);
            }
        } else if (TagIs(tok, "buChar")) {
            AttrInfo* ch = tok->GetAttrByName("char");
            if (ch && ch->valLen > 0) {
                ls.hasBullet = true;
                ls.bulletIsNone = false;
                str::Free(ls.bulletChar);
                ls.bulletChar = str::Dup(ch->val, ch->valLen);
            }
        } else if (TagIs(tok, "buAutoNum")) {
            ls.hasBullet = true;
            ls.bulletIsNone = false;
        } else if (TagIs(tok, "buNone")) {
            ls.bulletIsNone = true;
            ls.hasBullet = false;
        } else if (TagIs(tok, "buSzPct")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                ls.bulletSzPct = ParseAttrFloat(v) / 1000.0f; // val in 1/1000 %
            }
        } else if (TagIs(tok, "buClr")) {
            if (!isSelf) {
                COLORREF c = ParseColorElement(parser, "buClr", theme);
                if (c != (COLORREF)-1) {
                    ls.bulletColor = c;
                }
            }
        } else if (TagIs(tok, "defRPr")) {
            inDefRPr = true;
            AttrInfo* sz = tok->GetAttrByName("sz");
            if (sz) {
                ls.fontSize = ParseAttrFloat(sz) / 100.0f;
            }
            AttrInfo* b = tok->GetAttrByName("b");
            if (b) {
                ls.bold = ParseAttrBool(b);
            }
            AttrInfo* i2 = tok->GetAttrByName("i");
            if (i2) {
                ls.italic = ParseAttrBool(i2);
            }
        } else if (inDefRPr && TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                ls.color = c;
            }
        } else if (inDefRPr && TagIs(tok, "latin")) {
            AttrInfo* tf = tok->GetAttrByName("typeface");
            if (tf && tf->valLen > 0) {
                str::Free(ls.fontName);
                ls.fontName = str::Dup(tf->val, tf->valLen);
            }
        }
    }
}

// Parse slide master XML and extract <p:txStyles>.
static PptxTxStyles* ParseMasterTxStyles(MultiFormatArchive* archive, const char* masterPath, const PptxTheme* theme) {
    ByteSlice data = archive->GetFileDataByName(masterPath);
    if (!data) {
        return nullptr;
    }
    auto* styles = new PptxTxStyles();
    HtmlPullParser parser(data);
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (!tok->IsStartTag()) {
            continue;
        }
        if (TagIs(tok, "titleStyle")) {
            ParseTxStyleLevels(parser, "titleStyle", styles->titleLevels, theme);
        } else if (TagIs(tok, "bodyStyle")) {
            ParseTxStyleLevels(parser, "bodyStyle", styles->bodyLevels, theme);
        } else if (TagIs(tok, "otherStyle")) {
            ParseTxStyleLevels(parser, "otherStyle", styles->otherLevels, theme);
        }
    }
    data.Free();
    return styles;
}

// ===== Run Properties Parser =====
// Parses attributes and children of <a:rPr> into a PptxTextRun.
static void ParseRunProps(HtmlToken* rprTok, HtmlPullParser& parser, PptxTextRun* run, const PptxTheme* theme) {
    // Attributes on <a:rPr>
    AttrInfo* sz = rprTok->GetAttrByName("sz");
    float szVal = ParseAttrFloat(sz);
    AttrInfo* b = rprTok->GetAttrByName("b");
    bool boldVal = ParseAttrBool(b);
    AttrInfo* i = rprTok->GetAttrByName("i");
    bool italicVal = ParseAttrBool(i);
    AttrInfo* u = rprTok->GetAttrByName("u");
    bool ulVal = u && u->valLen > 0 && !str::EqNI(u->val, "none", u->valLen);
    AttrInfo* strike = rprTok->GetAttrByName("strike");
    bool strikeVal = strike && strike->valLen > 0 && !str::EqNI(strike->val, "noStrike", strike->valLen);
    AttrInfo* spcAttr = rprTok->GetAttrByName("spc");

    if (szVal > 0) {
        run->fontSize = szVal / 100.0f; // sz in hundredths of a point
    }
    if (b) {
        run->bold = boldVal;
    }
    if (i) {
        run->italic = italicVal;
    }
    if (u) {
        run->underline = ulVal;
    }
    if (strike) {
        run->strikethrough = strikeVal;
    }
    if (spcAttr && spcAttr->valLen > 0) {
        run->spc = (int)ParseAttrI64(spcAttr); // hundredths of a point
    }

    // Children: solidFill, latin font, etc.
    // (only if not a self-closing tag)
    if (rprTok->IsEmptyElementEndTag()) {
        return;
    }
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag() && TagIs(tok, "rPr")) {
            break;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }
        if (TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                run->color = c;
            }
        } else if (TagIs(tok, "latin")) {
            AttrInfo* tf = tok->GetAttrByName("typeface");
            if (tf && tf->valLen > 0) {
                // "+mj-lt" = major (heading) font, "+mn-lt" = minor (body) font → resolved later
                str::Free(run->fontName);
                run->fontName = str::Dup(tf->val, tf->valLen);
            }
        }
        // noFill, gradFill, ln, effectLst — ignored for now
    }
}

// ===== Paragraph Properties Parser =====
static void ParseParaProps(HtmlToken* pprTok, HtmlPullParser& parser, PptxParaProps& props, const PptxTheme* theme) {
    // Attributes on <a:pPr>
    AttrInfo* algn = pprTok->GetAttrByName("algn");
    if (algn) {
        if (str::EqNI(algn->val, "ctr", algn->valLen)) {
            props.algn = 1;
        } else if (str::EqNI(algn->val, "r", algn->valLen)) {
            props.algn = 2;
        } else if (str::EqNI(algn->val, "just", algn->valLen)) {
            props.algn = 3;
        } else {
            props.algn = 0; // "l" or default
        }
    }
    AttrInfo* marL = pprTok->GetAttrByName("marL");
    if (marL) {
        props.marL = ParseAttrI64(marL);
    }
    AttrInfo* indent = pprTok->GetAttrByName("indent");
    if (indent) {
        props.indent = ParseAttrI64(indent);
    }
    AttrInfo* lvl = pprTok->GetAttrByName("lvl");
    if (lvl) {
        props.lvl = (int)ParseAttrI64(lvl);
    }

    if (pprTok->IsEmptyElementEndTag()) {
        return;
    }
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag() && TagIs(tok, "pPr")) {
            break;
        }
        bool isSelf = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelf) {
            continue;
        }
        if (TagIs(tok, "lnSpc")) {
            // child: <a:spcPct val="..."/> or <a:spcPts val="..."/>
            HtmlToken* inner;
            while ((inner = parser.Next()) != nullptr) {
                if (inner->IsError() || (inner->IsEndTag() && TagIs(inner, "lnSpc"))) {
                    break;
                }
                if (inner->IsStartTag() || inner->IsEmptyElementEndTag()) {
                    if (TagIs(inner, "spcPct")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.lnSpcPct = ParseAttrFloat(v) / 1000.0f; // val in 1/1000 %
                        }
                    } else if (TagIs(inner, "spcPts")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.lnSpcPts = ParseAttrFloat(v) / 100.0f; // val in 1/100 points
                        }
                    }
                }
            }
        } else if (TagIs(tok, "spcBef")) {
            HtmlToken* inner;
            while ((inner = parser.Next()) != nullptr) {
                if (inner->IsError() || (inner->IsEndTag() && TagIs(inner, "spcBef"))) {
                    break;
                }
                if (inner->IsStartTag() || inner->IsEmptyElementEndTag()) {
                    if (TagIs(inner, "spcPts")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.spcBefPt = ParseAttrFloat(v) / 100.0f; // hundredths of a point
                        }
                    } else if (TagIs(inner, "spcPct")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.spcBefPct = ParseAttrFloat(v) / 1000.0f; // 1/1000 %
                        }
                    }
                }
            }
        } else if (TagIs(tok, "spcAft")) {
            HtmlToken* inner;
            while ((inner = parser.Next()) != nullptr) {
                if (inner->IsError() || (inner->IsEndTag() && TagIs(inner, "spcAft"))) {
                    break;
                }
                if (inner->IsStartTag() || inner->IsEmptyElementEndTag()) {
                    if (TagIs(inner, "spcPts")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.spcAftPt = ParseAttrFloat(v) / 100.0f;
                        }
                    } else if (TagIs(inner, "spcPct")) {
                        AttrInfo* v = inner->GetAttrByName("val");
                        if (v) {
                            props.spcAftPct = ParseAttrFloat(v) / 1000.0f;
                        }
                    }
                }
            }
        } else if (TagIs(tok, "buNone")) {
            props.hasBullet = false;
            props.bulletIsNone = true;
        } else if (TagIs(tok, "buChar")) {
            AttrInfo* ch = tok->GetAttrByName("char");
            if (ch && ch->valLen > 0) {
                props.hasBullet = true;
                props.bulletIsNone = false;
                str::Free(props.bulletCharStr);
                props.bulletCharStr = str::Dup(ch->val, ch->valLen);
            }
        } else if (TagIs(tok, "buAutoNum")) {
            props.hasBullet = true;
            props.bulletIsNone = false;
            props.bulletAutoNum = true;
            AttrInfo* startAt = tok->GetAttrByName("startAt");
            if (startAt) {
                props.bulletAutoNumStart = (int)ParseAttrI64(startAt);
            }
        } else if (TagIs(tok, "buFont")) {
            AttrInfo* tf = tok->GetAttrByName("typeface");
            if (tf && tf->valLen > 0) {
                str::Free(props.buFontName);
                props.buFontName = str::Dup(tf->val, tf->valLen);
            }
        } else if (TagIs(tok, "buClr")) {
            if (!isSelf) {
                COLORREF c = ParseColorElement(parser, "buClr", theme);
                if (c != (COLORREF)-1) {
                    props.buColor = c;
                }
            }
        } else if (TagIs(tok, "buSzPct")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                props.buSzPct = ParseAttrFloat(v) / 1000.0f; // val in 1/1000 %
            }
        } else if (TagIs(tok, "buSzPts")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                props.buSzPts = ParseAttrFloat(v) / 100.0f; // val in hundredths of a point
            }
        } else if (TagIs(tok, "defRPr")) {
            // Default run properties for this paragraph
            AttrInfo* sz = tok->GetAttrByName("sz");
            if (sz) {
                props.defFontSize = ParseAttrFloat(sz) / 100.0f;
            }
            AttrInfo* b2 = tok->GetAttrByName("b");
            if (b2) {
                props.defBold = ParseAttrBool(b2);
            }
            AttrInfo* i2 = tok->GetAttrByName("i");
            if (i2) {
                props.defItalic = ParseAttrBool(i2);
            }
            // Color in defRPr children
            if (!tok->IsEmptyElementEndTag()) {
                HtmlToken* inner;
                while ((inner = parser.Next()) != nullptr) {
                    if (inner->IsError() || (inner->IsEndTag() && TagIs(inner, "defRPr"))) {
                        break;
                    }
                    if ((inner->IsStartTag() || inner->IsEmptyElementEndTag()) && TagIs(inner, "solidFill")) {
                        COLORREF c = ParseColorBlock(parser, theme);
                        if (c != (COLORREF)-1) {
                            props.defColor = c;
                        }
                    } else if ((inner->IsStartTag() || inner->IsEmptyElementEndTag()) && TagIs(inner, "latin")) {
                        AttrInfo* tf = inner->GetAttrByName("typeface");
                        if (tf && tf->valLen > 0) {
                            str::Free(props.defFont);
                            props.defFont = str::Dup(tf->val, tf->valLen);
                        }
                    }
                }
            }
        }
    }
}

// ===== Text Body Properties Parser =====
static void ParseBodyProps(HtmlToken* bodyTok, HtmlPullParser& parser, PptxBodyProps& bp) {
    // Attributes on <a:bodyPr>
    AttrInfo* lIns = bodyTok->GetAttrByNameNS("lIns", nullptr);
    i64 lv = ParseAttrI64(lIns);
    AttrInfo* rIns = bodyTok->GetAttrByNameNS("rIns", nullptr);
    i64 rv = ParseAttrI64(rIns);
    AttrInfo* tIns = bodyTok->GetAttrByNameNS("tIns", nullptr);
    i64 tv = ParseAttrI64(tIns);
    AttrInfo* bIns = bodyTok->GetAttrByNameNS("bIns", nullptr);
    i64 bv = ParseAttrI64(bIns);
    if (lIns) {
        bp.lIns = lv;
    }
    if (rIns) {
        bp.rIns = rv;
    }
    if (tIns) {
        bp.tIns = tv;
    }
    if (bIns) {
        bp.bIns = bv;
    }

    AttrInfo* anchor = bodyTok->GetAttrByName("anchor");
    if (anchor) {
        if (str::EqNI(anchor->val, "ctr", anchor->valLen)) {
            bp.anchor = 1;
        } else if (str::EqNI(anchor->val, "b", anchor->valLen)) {
            bp.anchor = 2;
        } else {
            bp.anchor = 0;
        }
    }
    AttrInfo* wrap = bodyTok->GetAttrByName("wrap");
    if (wrap) {
        bp.wrap = !str::EqNI(wrap->val, "none", wrap->valLen);
    }
    AttrInfo* vert = bodyTok->GetAttrByName("vert");
    if (vert) {
        bp.vert = vert->valLen > 0 && !str::EqNI(vert->val, "horz", vert->valLen);
    }

    // Parse children for normAutofit fontScale
    if (!bodyTok->IsEmptyElementEndTag()) {
        HtmlToken* tok;
        while ((tok = parser.Next()) != nullptr) {
            if (tok->IsError() || (tok->IsEndTag() && TagIs(tok, "bodyPr"))) {
                break;
            }
            if ((tok->IsStartTag() || tok->IsEmptyElementEndTag()) && TagIs(tok, "normAutofit")) {
                AttrInfo* fs = tok->GetAttrByName("fontScale");
                if (fs) {
                    bp.fontScale = ParseAttrFloat(fs) / 1000.0f; // val in 1/1000 % → %
                }
                AttrInfo* lsr = tok->GetAttrByName("lnSpcReduction");
                if (lsr) {
                    bp.lnSpcReduction = ParseAttrFloat(lsr) / 1000.0f;
                }
            }
        }
    }
}

// ===== Line/Border Properties Parser =====
// Parses <a:ln> element — width, solid fill color, or noFill.
static void ParseLineProps(HtmlToken* lnTok, HtmlPullParser& parser, float& outWidth, COLORREF& outColor,
                           bool& outNoFill, const PptxTheme* theme) {
    AttrInfo* w = lnTok->GetAttrByName("w");
    outWidth = (w && w->valLen > 0) ? ParseAttrFloat(w) : 9525.0f; // default ~0.75pt
    outColor = (COLORREF)-1;
    outNoFill = false;
    if (lnTok->IsEmptyElementEndTag()) {
        return;
    }
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError() || (tok->IsEndTag() && TagIs(tok, "ln"))) {
            break;
        }
        if (!tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
            continue;
        }
        if (TagIs(tok, "noFill")) {
            outNoFill = true;
        } else if (TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                outColor = c;
            }
        }
        // gradFill, prstDash, round, miter, bevel — ignored for now
    }
}

// ===== Slide XML Parser =====

// Helper: finalize a shape — apply group transforms then append to slide.
static void FinalizeShape(PptxShape* shape, PptxSlide* slide, const Vec<GroupTransform>& groupStack,
                          const GroupTransform& curGroup, bool inGrpSp, const Vec<PlaceholderPos*>& phTable) {
    if (!shape) {
        return;
    }
    // If no explicit xfrm, try to inherit position from layout/master placeholder
    if (!shape->hasExplicitXfrm && (shape->phIdx >= 0 || shape->phType)) {
        const PlaceholderPos* ph = LookupPhPos(phTable, shape->phIdx, shape->phType);
        if (ph) {
            shape->offX = ph->offX;
            shape->offY = ph->offY;
            shape->extCx = ph->extCx;
            shape->extCy = ph->extCy;
        }
        // Inherit default text formatting: scan ALL matching entries (layout+master)
        // to find the first one with a font size (layout is first, master is appended after)
        for (PlaceholderPos* p : phTable) {
            if (p->defFontSize <= 0 || shape->phDefFontSize > 0) {
                continue;
            }
            bool matchIdx = (p->idx >= 0 && p->idx == shape->phIdx);
            bool matchType = (p->phType && shape->phType && str::EqI(p->phType, shape->phType));
            if (matchIdx || matchType) {
                shape->phDefFontSize = p->defFontSize;
                shape->phDefBold = p->defBold;
            }
        }
    }
    // Apply innermost group transform first, then outer ones
    if (inGrpSp && curGroup.valid) {
        ApplyGroupTransform(curGroup, shape->offX, shape->offY, shape->extCx, shape->extCy);
    }
    for (int gi = groupStack.Size() - 1; gi >= 0; gi--) {
        ApplyGroupTransform(groupStack[gi], shape->offX, shape->offY, shape->extCx, shape->extCy);
    }
    // Keep shapes with valid size (includes inherited ph positions), image, connector, or custGeom
    bool hasSize = (shape->extCx > 0 && shape->extCy > 0);
    bool isImage = (shape->type == PptxShapeType::Image) || (shape->imagePath != nullptr);
    bool isConn = (shape->type == PptxShapeType::Connector);
    bool hasCustGeom = shape->custPaths.size() > 0;
    if (hasSize || isImage || isConn || hasCustGeom) {
        slide->shapes.Append(shape);
    } else {
        delete shape;
    }
}

// Extract background color from a slide layout or master XML.
static COLORREF ExtractBgColor(MultiFormatArchive* archive, const char* xmlPath, const PptxTheme* theme) {
    ByteSlice data = archive->GetFileDataByName(xmlPath);
    if (!data) {
        return (COLORREF)-1;
    }
    HtmlPullParser parser(data);
    HtmlToken* tok;
    bool inBg = false;
    bool inBgPr = false;
    bool inBgRef = false;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsEndTag()) {
            if (TagIs(tok, "bg")) {
                inBg = false;
            }
            if (TagIs(tok, "bgPr")) {
                inBgPr = false;
            }
            if (TagIs(tok, "bgRef")) {
                inBgRef = false;
            }
            continue;
        }
        if (!tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
            continue;
        }
        if (TagIs(tok, "bg")) {
            inBg = true;
        } else if (inBg && TagIs(tok, "bgPr")) {
            inBgPr = true;
        } else if (inBg && TagIs(tok, "bgRef")) {
            inBgRef = true;
        } else if (inBgPr && TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            data.Free();
            return c;
        } else if ((inBgRef || inBgPr) && TagIs(tok, "srgbClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v) {
                COLORREF c = ParseHexColor(v->val, v->valLen);
                data.Free();
                return c;
            }
        } else if ((inBgRef || inBgPr) && TagIs(tok, "schemeClr")) {
            AttrInfo* v = tok->GetAttrByName("val");
            if (v && theme) {
                COLORREF c = theme->GetSchemeColor(v->val, v->valLen);
                data.Free();
                return c;
            }
        } else if ((inBgRef || inBgPr) && TagIs(tok, "sysClr")) {
            AttrInfo* lc = tok->GetAttrByName("lastClr");
            if (lc) {
                COLORREF c = ParseHexColor(lc->val, lc->valLen);
                data.Free();
                return c;
            }
        }
    }
    data.Free();
    return (COLORREF)-1;
}

// Build a table of placeholder positions by loading the slide's layout and master.
// Also extracts the inherited background color from layout/master if available.
static void BuildPlaceholderTable(MultiFormatArchive* archive, const char* slideZipPath, Vec<PlaceholderPos*>& phTable,
                                  const PptxTheme* theme = nullptr, COLORREF* outInheritedBg = nullptr) {
    Vec<char*> slideRelRIds, slideRelPaths;
    ParseSlideRels(archive, slideZipPath, slideRelRIds, slideRelPaths);

    // Find the slideLayout relationship
    const char* layoutPath = nullptr;
    for (int i = 0; i < slideRelPaths.Size(); i++) {
        if (str::Find(slideRelPaths[i], "slideLayout")) {
            layoutPath = slideRelPaths[i];
            break;
        }
    }
    const char* masterPath = nullptr;
    if (layoutPath) {
        ExtractPlaceholderPositions(archive, layoutPath, phTable);

        // Now find master from the layout's rels
        Vec<char*> layoutRelRIds, layoutRelPaths;
        ParseSlideRels(archive, layoutPath, layoutRelRIds, layoutRelPaths);
        for (int i = 0; i < layoutRelPaths.Size(); i++) {
            if (str::Find(layoutRelPaths[i], "slideMaster")) {
                masterPath = layoutRelPaths[i];
                ExtractPlaceholderPositions(archive, masterPath, phTable);
                break;
            }
        }
        // Extract inherited background: try layout first, then master
        if (outInheritedBg) {
            COLORREF bg = ExtractBgColor(archive, layoutPath, theme);
            if (bg == (COLORREF)-1 && masterPath) {
                bg = ExtractBgColor(archive, masterPath, theme);
            }
            *outInheritedBg = bg;
        }
        for (char* p : layoutRelRIds) {
            str::Free(p);
        }
        for (char* p : layoutRelPaths) {
            str::Free(p);
        }
    }
    for (char* p : slideRelRIds) {
        str::Free(p);
    }
    for (char* p : slideRelPaths) {
        str::Free(p);
    }
}

static PptxSlide* ParseSlide(MultiFormatArchive* archive, const char* slideZipPath, const PptxTheme* theme) {
    ByteSlice data = archive->GetFileDataByName(slideZipPath);
    if (!data) {
        return nullptr;
    }

    Vec<char*> relRIds, relPaths;
    ParseSlideRels(archive, slideZipPath, relRIds, relPaths);

    // Build placeholder position table from layout/master + inherited background
    Vec<PlaceholderPos*> phTable;
    COLORREF inheritedBg = (COLORREF)-1;
    BuildPlaceholderTable(archive, slideZipPath, phTable, theme, &inheritedBg);

    auto* slide = new PptxSlide();
    PptxShape* curShape = nullptr;
    PptxPara* curPara = nullptr;
    PptxTextRun* curRun = nullptr;
    bool nextTextIsRunContent = false;
    bool inSpPr = false;
    bool inSpTree = false;
    bool inTxBody = false;
    bool inBg = false;
    bool inBgPr = false;
    bool inCustGeom = false;
    PptxCustPath* curCustPath = nullptr;
    PptxPathCmdType curCmdType = PptxPathCmdType::MoveTo;
    bool inPathCmd = false; // expecting <a:pt> for current cmd
    // Group shape tracking
    bool inGrpSp = false;
    bool inGrpSpPr = false;
    GroupTransform curGroup;
    Vec<GroupTransform> groupStack; // outer groups when nesting
    int bulletCounterForSlide = 0;

    // mc:AlternateContent: skip mc:Choice (OMML/complex), process mc:Fallback (plain text)
    bool inAltChoice = false;
    int altChoiceDepth = 0; // track nested tags inside Choice

    // p:graphicFrame: OLE objects / charts — extract image preview if present
    bool inGraphicFrame = false;
    PptxShape* gfShape = nullptr;

    // Table parsing state
    bool inTable = false;
    bool inTableRow = false;
    bool inTableCell = false;
    bool inTcPr = false;
    Vec<i64> tableColWidths;
    i64 tableOffX = 0, tableOffY = 0;
    i64 tableCurRowH = 0;
    i64 tableCurY = 0;
    int tableCurCol = 0;
    int tableCellGridSpan = 1;

    HtmlPullParser parser(data);
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }

        // ---- mc:AlternateContent: skip mc:Choice (OMML), process mc:Fallback ----
        // Track when we're inside <mc:Choice> and suppress all shape parsing.
        if (inAltChoice) {
            if (tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
                altChoiceDepth++;
            } else if (tok->IsEndTag()) {
                if (altChoiceDepth > 0) {
                    altChoiceDepth--;
                } else {
                    // </mc:Choice> itself
                    inAltChoice = false;
                }
            }
            continue; // skip everything inside Choice
        }
        if (tok->IsStartTag() && TagIs(tok, "Choice")) {
            inAltChoice = true;
            altChoiceDepth = 0;
            continue;
        }
        // <mc:Fallback> and </mc:AlternateContent> — just let normal parsing handle content

        // ---- End tags ----
        if (tok->IsEndTag()) {
            if (TagIs(tok, "sp") || TagIs(tok, "pic") || TagIs(tok, "cxnSp")) {
                FinalizeShape(curShape, slide, groupStack, curGroup, inGrpSp, phTable);
                curShape = nullptr;
                curPara = nullptr;
                curRun = nullptr;
                inSpPr = false;
                inTxBody = false;
            } else if (TagIs(tok, "grpSp")) {
                // Pop group from stack
                inGrpSp = !groupStack.IsEmpty();
                if (!groupStack.IsEmpty()) {
                    curGroup = groupStack.Pop();
                } else {
                    curGroup = GroupTransform{};
                    inGrpSp = false;
                }
                inGrpSpPr = false;
            } else if (TagIs(tok, "grpSpPr")) {
                inGrpSpPr = false;
            } else if (TagIs(tok, "p")) {
                curPara = nullptr;
            } else if (TagIs(tok, "r") || TagIs(tok, "fld")) {
                curRun = nullptr;
                nextTextIsRunContent = false;
            } else if (TagIs(tok, "spPr")) {
                inSpPr = false;
            } else if (TagIs(tok, "custGeom")) {
                inCustGeom = false;
                curCustPath = nullptr;
                inPathCmd = false;
            } else if (TagIs(tok, "path") && inCustGeom) {
                curCustPath = nullptr;
            } else if (TagIs(tok, "txBody")) {
                inTxBody = false;
            } else if (TagIs(tok, "spTree")) {
                inSpTree = false;
            } else if (TagIs(tok, "bg")) {
                inBg = false;
            } else if (TagIs(tok, "bgPr")) {
                inBgPr = false;
            } else if (inTable && TagIs(tok, "tc")) {
                // Finalize table cell shape
                if (curShape) {
                    slide->shapes.Append(curShape);
                    curShape = nullptr;
                }
                curPara = nullptr;
                curRun = nullptr;
                inTxBody = false;
                inSpPr = false;
                inTcPr = false;
                inTableCell = false;
                // Advance column by gridSpan
                tableCurCol += tableCellGridSpan;
                tableCellGridSpan = 1;
            } else if (inTable && TagIs(tok, "tcPr")) {
                inTcPr = false;
            } else if (inTable && TagIs(tok, "tr")) {
                inTableRow = false;
                tableCurY += tableCurRowH;
                tableCurCol = 0;
            } else if (TagIs(tok, "tbl")) {
                inTable = false;
                tableColWidths.Reset();
            } else if (TagIs(tok, "graphicFrame")) {
                // Finalize OLE/chart graphic frame as image shape
                if (gfShape) {
                    if (gfShape->imagePath) {
                        FinalizeShape(gfShape, slide, groupStack, curGroup, inGrpSp, phTable);
                    } else {
                        delete gfShape;
                    }
                    gfShape = nullptr;
                }
                inGraphicFrame = false;
                inTable = false;
                tableColWidths.Reset();
            }
            continue;
        }

        // ---- Text nodes ----
        if (!tok->IsStartTag() && !tok->IsEmptyElementEndTag()) {
            if (nextTextIsRunContent && curRun && tok->IsText()) {
                TempStr decoded = ResolveHtmlEntitiesTemp(tok->s, tok->sLen);
                str::Free(curRun->text);
                curRun->text = str::Dup(decoded ? decoded : "");
                nextTextIsRunContent = false;
            }
            continue;
        }

        // ---- Start / self-closing tags ----

        // Background
        if (TagIs(tok, "bg")) {
            inBg = true;
        } else if (inBg && TagIs(tok, "bgPr")) {
            inBgPr = true;
        } else if (inBgPr && TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                slide->bgColor = c;
            }
        } else if (inBgPr && TagIs(tok, "blipFill")) {
            // Background image — will be resolved when <a:blip r:embed=> is seen
        } else if (inBgPr && TagIs(tok, "blip")) {
            AttrInfo* embed = tok->GetAttrByNameNS("embed", nullptr);
            if (embed) {
                AutoFreeStr rId(str::Dup(embed->val, embed->valLen));
                const char* imgPath = LookupRId(relRIds, relPaths, rId.data);
                if (imgPath) {
                    str::Free(slide->bgImagePath);
                    slide->bgImagePath = str::Dup(imgPath);
                }
            }
        }

        // Shape tree + group shapes
        else if (TagIs(tok, "spTree")) {
            inSpTree = true;
        } else if (inSpTree && TagIs(tok, "grpSp")) {
            // Nested group: push existing curGroup, start new one
            if (inGrpSp) {
                groupStack.Append(curGroup);
            }
            inGrpSp = true;
            curGroup = GroupTransform{};
            inGrpSpPr = false;
        } else if (inGrpSp && !curShape && TagIs(tok, "grpSpPr")) {
            inGrpSpPr = true;
        }

        // Group shape properties (chOff/chExt/off/ext)
        else if (inGrpSpPr && TagIs(tok, "off")) {
            curGroup.offX = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
            curGroup.offY = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
        } else if (inGrpSpPr && TagIs(tok, "ext")) {
            curGroup.extCx = ParseAttrI64(tok->GetAttrByNameNS("cx", nullptr));
            curGroup.extCy = ParseAttrI64(tok->GetAttrByNameNS("cy", nullptr));
        } else if (inGrpSpPr && TagIs(tok, "chOff")) {
            curGroup.chOffX = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
            curGroup.chOffY = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
        } else if (inGrpSpPr && TagIs(tok, "chExt")) {
            curGroup.chExtCx = ParseAttrI64(tok->GetAttrByNameNS("cx", nullptr));
            curGroup.chExtCy = ParseAttrI64(tok->GetAttrByNameNS("cy", nullptr));
            curGroup.valid = true;
        }

        // Individual shape start tags
        else if (inSpTree && TagIs(tok, "sp")) {
            curShape = new PptxShape();
            curShape->type = PptxShapeType::Text;
            inSpPr = false;
            inTxBody = false;
        } else if (inSpTree && TagIs(tok, "pic")) {
            curShape = new PptxShape();
            curShape->type = PptxShapeType::Image;
            inSpPr = false;
            inTxBody = false;
        } else if (inSpTree && TagIs(tok, "cxnSp")) {
            curShape = new PptxShape();
            curShape->type = PptxShapeType::Connector;
            inSpPr = false;
            inTxBody = false;
        }

        // p:graphicFrame — OLE objects (equations, charts) with optional image preview
        else if (inSpTree && TagIs(tok, "graphicFrame")) {
            inGraphicFrame = true;
            gfShape = new PptxShape();
            gfShape->type = PptxShapeType::Image;
        } else if (inGraphicFrame && gfShape && TagIs(tok, "off") && !curShape) {
            gfShape->offX = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
            gfShape->offY = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
        } else if (inGraphicFrame && gfShape && TagIs(tok, "ext") && !curShape) {
            gfShape->extCx = ParseAttrI64(tok->GetAttrByNameNS("cx", nullptr));
            gfShape->extCy = ParseAttrI64(tok->GetAttrByNameNS("cy", nullptr));
        } else if (inGraphicFrame && gfShape && TagIs(tok, "blip") && !inTable) {
            // OLE object image preview (inside p:oleObj/p:pic/p:blipFill/a:blip)
            AttrInfo* embed = tok->GetAttrByNameNS("embed", nullptr);
            if (embed && embed->valLen > 0) {
                AutoFreeStr rId(str::Dup(embed->val, embed->valLen));
                const char* imgPath = LookupRId(relRIds, relPaths, rId.data);
                if (imgPath && !gfShape->imagePath) {
                    gfShape->imagePath = str::Dup(imgPath);
                }
            }
        }

        // ---- Table inside graphicFrame ----
        else if (inGraphicFrame && TagIs(tok, "tbl")) {
            inTable = true;
            tableColWidths.Reset();
            tableOffX = gfShape ? gfShape->offX : 0;
            tableOffY = gfShape ? gfShape->offY : 0;
            tableCurY = 0;
            tableCurCol = 0;
            // We found a table, so the gfShape is not an image preview
            if (gfShape) {
                delete gfShape;
                gfShape = nullptr;
            }
        } else if (inTable && TagIs(tok, "gridCol")) {
            AttrInfo* w = tok->GetAttrByName("w");
            if (w) {
                tableColWidths.Append(ParseAttrI64(w));
            }
        } else if (inTable && TagIs(tok, "tr")) {
            inTableRow = true;
            AttrInfo* h = tok->GetAttrByName("h");
            tableCurRowH = h ? ParseAttrI64(h) : 370840; // default ~0.4"
            tableCurCol = 0;
        } else if (inTable && inTableRow && TagIs(tok, "tc")) {
            inTableCell = true;
            inTcPr = false;
            // Check for hMerge/vMerge (skip merged continuation cells)
            AttrInfo* hMerge = tok->GetAttrByName("hMerge");
            AttrInfo* vMerge = tok->GetAttrByName("vMerge");
            bool isMerged = (hMerge && ParseAttrBool(hMerge)) || (vMerge && ParseAttrBool(vMerge));
            // Check gridSpan
            AttrInfo* gs = tok->GetAttrByName("gridSpan");
            tableCellGridSpan = gs ? (int)ParseAttrI64(gs) : 1;
            if (tableCellGridSpan < 1) {
                tableCellGridSpan = 1;
            }

            // Calculate cell position from grid
            i64 cellX = tableOffX;
            for (int ci = 0; ci < tableCurCol && ci < tableColWidths.Size(); ci++) {
                cellX += tableColWidths[ci];
            }
            i64 cellW = 0;
            for (int ci = tableCurCol; ci < tableCurCol + tableCellGridSpan && ci < tableColWidths.Size(); ci++) {
                cellW += tableColWidths[ci];
            }
            i64 cellY = tableOffY + tableCurY;
            i64 cellH = tableCurRowH;

            if (!isMerged && cellW > 0 && cellH > 0) {
                curShape = new PptxShape();
                curShape->type = PptxShapeType::Text;
                curShape->offX = cellX;
                curShape->offY = cellY;
                curShape->extCx = cellW;
                curShape->extCy = cellH;
                curShape->hasExplicitXfrm = true;
                // Default thin border for table cells
                curShape->borderWidth = 12700.0f; // ~1pt
                curShape->borderColor = RGB(0, 0, 0);
                // Default cell insets (smaller than shape defaults)
                curShape->bodyProps.lIns = 45720; // ~0.05"
                curShape->bodyProps.rIns = 45720;
                curShape->bodyProps.tIns = 22860;
                curShape->bodyProps.bIns = 22860;
            }
        } else if (inTable && inTableCell && TagIs(tok, "tcPr")) {
            inTcPr = true;
        } else if (inTable && inTcPr && curShape && TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                curShape->fillColor = c;
            }
        } else if (inTable && inTcPr && curShape && TagIs(tok, "noFill")) {
            curShape->fillColor = (COLORREF)-1;
        }

        // Placeholder tag — record ph idx/type on current shape
        else if (curShape && TagIs(tok, "ph")) {
            AttrInfo* pidx = tok->GetAttrByName("idx");
            if (pidx) {
                curShape->phIdx = (int)ParseAttrI64(pidx);
            } else if (curShape->phIdx < 0) {
                curShape->phIdx = 0; // idx defaults to 0 if absent (title-like)
            }
            AttrInfo* ptype = tok->GetAttrByName("type");
            if (ptype && ptype->valLen > 0) {
                str::Free(curShape->phType);
                curShape->phType = str::Dup(ptype->val, ptype->valLen);
            }
        }

        // Shape properties: geometry, rotation, fill, border
        else if (curShape && TagIs(tok, "spPr")) {
            inSpPr = true;
        } else if (curShape && inSpPr && TagIs(tok, "xfrm")) {
            curShape->hasExplicitXfrm = true;
            // Read rotation and flip attributes from <a:xfrm>
            AttrInfo* r = tok->GetAttrByName("rot");
            if (r) {
                curShape->rot = (int)ParseAttrI64(r);
            }
            AttrInfo* fH = tok->GetAttrByName("flipH");
            if (fH) {
                curShape->flipH = ParseAttrBool(fH);
            }
            AttrInfo* fV = tok->GetAttrByName("flipV");
            if (fV) {
                curShape->flipV = ParseAttrBool(fV);
            }
        } else if (curShape && inSpPr && TagIs(tok, "off")) {
            curShape->offX = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
            curShape->offY = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
        } else if (curShape && inSpPr && TagIs(tok, "ext")) {
            curShape->extCx = ParseAttrI64(tok->GetAttrByNameNS("cx", nullptr));
            curShape->extCy = ParseAttrI64(tok->GetAttrByNameNS("cy", nullptr));
        } else if (curShape && inSpPr && TagIs(tok, "noFill")) {
            // Explicit transparent fill — ensure no rectangle is painted
            curShape->fillColor = (COLORREF)-1;
        } else if (curShape && inSpPr && TagIs(tok, "solidFill")) {
            COLORREF c = ParseColorBlock(parser, theme);
            if (c != (COLORREF)-1) {
                curShape->fillColor = c;
            }
        } else if (curShape && inSpPr && TagIs(tok, "gradFill")) {
            // Approximate gradient: collect gradient stop colors from <a:gs> elements,
            // pick the middle one.  OOXML structure is:
            //   <a:gradFill><a:gsLst><a:gs pos="..."><a:srgbClr val="..."/></a:gs>...
            if (!tok->IsEmptyElementEndTag()) {
                HtmlToken* gtok;
                Vec<COLORREF> stops;
                bool inGs = false;
                while ((gtok = parser.Next()) != nullptr) {
                    if (gtok->IsError() || (gtok->IsEndTag() && TagIs(gtok, "gradFill"))) {
                        break;
                    }
                    if (gtok->IsStartTag() && TagIs(gtok, "gs")) {
                        inGs = true;
                    } else if (gtok->IsEndTag() && TagIs(gtok, "gs")) {
                        inGs = false;
                    }
                    if (inGs && (gtok->IsStartTag() || gtok->IsEmptyElementEndTag())) {
                        if (TagIs(gtok, "srgbClr")) {
                            AttrInfo* v = gtok->GetAttrByName("val");
                            if (v) {
                                stops.Append(ParseHexColor(v->val, v->valLen));
                            }
                        } else if (TagIs(gtok, "schemeClr")) {
                            AttrInfo* v = gtok->GetAttrByName("val");
                            if (v && theme) {
                                stops.Append(theme->GetSchemeColor(v->val, v->valLen));
                            }
                        } else if (TagIs(gtok, "sysClr")) {
                            AttrInfo* lc = gtok->GetAttrByName("lastClr");
                            if (lc) {
                                stops.Append(ParseHexColor(lc->val, lc->valLen));
                            }
                        }
                    }
                }
                if (stops.Size() > 0) {
                    curShape->fillColor = stops[stops.Size() / 2];
                }
            }
        } else if (curShape && inSpPr && TagIs(tok, "ln")) {
            ParseLineProps(tok, parser, curShape->borderWidth, curShape->borderColor, curShape->noBorder, theme);
        } else if (curShape && inSpPr && TagIs(tok, "prstGeom")) {
            AttrInfo* prst = tok->GetAttrByName("prst");
            if (prst && prst->valLen > 0) {
                str::Free(curShape->prstGeom);
                curShape->prstGeom = str::Dup(prst->val, prst->valLen);
            }
        } else if (curShape && inSpPr && TagIs(tok, "custGeom")) {
            inCustGeom = true;
        } else if (curShape && inCustGeom && TagIs(tok, "path")) {
            curCustPath = new PptxCustPath();
            AttrInfo* aw = tok->GetAttrByName("w");
            AttrInfo* ah = tok->GetAttrByName("h");
            if (aw) {
                curCustPath->w = ParseAttrI64(aw);
            }
            if (ah) {
                curCustPath->h = ParseAttrI64(ah);
            }
            curShape->custPaths.Append(curCustPath);
        } else if (curCustPath && TagIs(tok, "moveTo")) {
            curCmdType = PptxPathCmdType::MoveTo;
            inPathCmd = true;
        } else if (curCustPath && TagIs(tok, "lnTo")) {
            curCmdType = PptxPathCmdType::LineTo;
            inPathCmd = true;
        } else if (curCustPath && TagIs(tok, "close")) {
            PptxPathCmd cmd;
            cmd.type = PptxPathCmdType::Close;
            curCustPath->cmds.Append(cmd);
        } else if (curCustPath && inPathCmd && TagIs(tok, "pt")) {
            PptxPathCmd cmd;
            cmd.type = curCmdType;
            cmd.pt.x = ParseAttrI64(tok->GetAttrByNameNS("x", nullptr));
            cmd.pt.y = ParseAttrI64(tok->GetAttrByNameNS("y", nullptr));
            curCustPath->cmds.Append(cmd);
            inPathCmd = false;
        }

        // Text body
        else if (curShape && TagIs(tok, "txBody")) {
            inTxBody = true;
        } else if (curShape && inTxBody && TagIs(tok, "bodyPr")) {
            ParseBodyProps(tok, parser, curShape->bodyProps);
        } else if (curShape && inTxBody && TagIs(tok, "p")) {
            curPara = new PptxPara();
            curShape->paras.Append(curPara);
            curRun = nullptr;
            bulletCounterForSlide++;
        } else if (curPara && TagIs(tok, "pPr")) {
            ParseParaProps(tok, parser, curPara->props, theme);
        } else if (curPara && (TagIs(tok, "r") || TagIs(tok, "fld"))) {
            curRun = new PptxTextRun();
            curPara->runs.Append(curRun);
            nextTextIsRunContent = false;
        } else if (curPara && TagIs(tok, "br")) {
            // Line break within paragraph
            auto* brRun = new PptxTextRun();
            brRun->text = str::Dup("\n");
            curPara->runs.Append(brRun);
        } else if (curRun && TagIs(tok, "rPr")) {
            ParseRunProps(tok, parser, curRun, theme);
        } else if (curRun && TagIs(tok, "t")) {
            nextTextIsRunContent = true;
        }

        // Image blip — handles both <p:pic><p:blipFill> and <p:sp><p:spPr><a:blipFill>
        else if (curShape && TagIs(tok, "blip")) {
            AttrInfo* embed = tok->GetAttrByNameNS("embed", nullptr);
            if (embed) {
                AutoFreeStr rId(str::Dup(embed->val, embed->valLen));
                const char* imgPath = LookupRId(relRIds, relPaths, rId.data);
                if (imgPath) {
                    str::Free(curShape->imagePath);
                    curShape->imagePath = str::Dup(imgPath);
                }
            }
        }
    }

    data.Free();
    for (char* p : relRIds) {
        str::Free(p);
    }
    for (char* p : relPaths) {
        str::Free(p);
    }
    DeleteVecMembers(phTable);

    // Apply inherited background from layout/master if slide doesn't define its own
    if (slide->bgColor == (COLORREF)-1 && !slide->bgImagePath && inheritedBg != (COLORREF)-1) {
        slide->bgColor = inheritedBg;
    }

    return slide;
}

// ===== Presentation XML Parser =====

static bool ParsePresentation(PptxDoc* doc) {
    // 1. Parse theme first (needed for color resolution)
    // Find theme path from ppt/_rels/presentation.xml.rels
    Vec<char*> relRIds, relPaths;
    ParseRels(doc->archive, "ppt/_rels/presentation.xml.rels", relRIds, relPaths);

    for (int i = 0; i < relPaths.Size(); i++) {
        // Theme relationship type contains "theme"
        if (str::Find(relPaths[i], "theme") && str::EndsWith(relPaths[i], ".xml")) {
            AutoFreeStr themePath;
            if (!str::StartsWith(relPaths[i], "ppt/")) {
                themePath.Set(str::Format("ppt/%s", relPaths[i]));
            } else {
                themePath.Set(str::Dup(relPaths[i]));
            }
            ParseTheme(doc, themePath.data);
            break;
        }
    }

    // 2. Parse presentation.xml for slide size and slide order
    ByteSlice data = doc->archive->GetFileDataByName("ppt/presentation.xml");
    if (!data) {
        for (char* p : relRIds) {
            str::Free(p);
        }
        for (char* p : relPaths) {
            str::Free(p);
        }
        return false;
    }

    Vec<char*> orderedRIds;
    bool inSldIdLst = false;

    HtmlPullParser parser(data);
    HtmlToken* tok;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        bool isSelfClose = tok->IsEmptyElementEndTag();
        bool isStart = tok->IsStartTag();
        if (!isStart && !isSelfClose) {
            continue;
        }
        if (TagIs(tok, "sldSz")) {
            AttrInfo* cx = tok->GetAttrByNameNS("cx", nullptr);
            i64 cxVal = ParseAttrI64(cx);
            AttrInfo* cy = tok->GetAttrByNameNS("cy", nullptr);
            i64 cyVal = ParseAttrI64(cy);
            if (cx) {
                doc->slideCx = cxVal;
            }
            if (cy) {
                doc->slideCy = cyVal;
            }
        } else if (TagIs(tok, "sldIdLst")) {
            inSldIdLst = true;
        } else if (inSldIdLst && TagIs(tok, "sldId")) {
            AttrInfo* rid = tok->GetAttrByName("r:id");
            if (!rid) {
                rid = tok->GetAttrByNameNS("id", nullptr);
                if (rid && rid->valLen > 0 && rid->val[0] != 'r') {
                    rid = nullptr;
                }
            }
            if (rid) {
                orderedRIds.Append(str::Dup(rid->val, rid->valLen));
            }
        } else if (tok->IsEndTag() && TagIs(tok, "sldIdLst")) {
            inSldIdLst = false;
        }
    }
    data.Free();

    // 3. Parse slide master text styles (<p:txStyles>) for default text formatting
    for (int i = 0; i < relPaths.Size(); i++) {
        if (str::Find(relPaths[i], "slideMaster") && str::EndsWith(relPaths[i], ".xml")) {
            AutoFreeStr masterPath;
            if (!str::StartsWith(relPaths[i], "ppt/")) {
                masterPath.Set(str::Format("ppt/%s", relPaths[i]));
            } else {
                masterPath.Set(str::Dup(relPaths[i]));
            }
            if (!doc->txStyles) {
                doc->txStyles = ParseMasterTxStyles(doc->archive, masterPath.data, doc->theme);
            }
            break;
        }
    }

    // 4. Build ordered slide paths from rIds
    for (char* rId : orderedRIds) {
        const char* target = LookupRId(relRIds, relPaths, rId);
        if (target) {
            if (!str::StartsWith(target, "ppt/")) {
                doc->slidePaths.Append(str::Format("ppt/%s", target));
            } else {
                doc->slidePaths.Append(str::Dup(target));
            }
        }
        str::Free(rId);
    }

    for (char* p : relRIds) {
        str::Free(p);
    }
    for (char* p : relPaths) {
        str::Free(p);
    }
    return doc->slidePaths.Size() > 0;
}

// ===== Document Properties Parser =====

static char* ExtractXmlText(const ByteSlice& data, const char* elemLocalName) {
    HtmlPullParser parser(data);
    HtmlToken* tok;
    bool inTarget = false;
    while ((tok = parser.Next()) != nullptr) {
        if (tok->IsError()) {
            break;
        }
        if (tok->IsStartTag() && TagIs(tok, elemLocalName)) {
            inTarget = true;
        } else if (tok->IsEndTag() && TagIs(tok, elemLocalName)) {
            inTarget = false;
        } else if (inTarget && tok->IsText()) {
            return str::Dup(tok->s, tok->sLen);
        }
    }
    return nullptr;
}

static void ParseDocProps(PptxDoc* doc) {
    ByteSlice coreData = doc->archive->GetFileDataByName("docProps/core.xml");
    if (!coreData) {
        coreData = doc->archive->GetFileDataByName("ppt/core.xml");
    }
    if (coreData) {
        AutoFree titleStr = ExtractXmlText(coreData, "title");
        if (titleStr.data) {
            AddProp(doc->props, kPropTitle, titleStr.data);
        }
        AutoFree creatorStr = ExtractXmlText(coreData, "creator");
        if (creatorStr.data) {
            AddProp(doc->props, kPropAuthor, creatorStr.data);
        }
        AutoFree createdStr = ExtractXmlText(coreData, "created");
        if (createdStr.data) {
            AddProp(doc->props, kPropCreationDate, createdStr.data);
        }
        AutoFree modifiedStr = ExtractXmlText(coreData, "modified");
        if (modifiedStr.data) {
            AddProp(doc->props, kPropModificationDate, modifiedStr.data);
        }
        coreData.Free();
    }
}

// ===== EnginePptx class =====

class EnginePptx : public EngineBase {
  public:
    EnginePptx();
    ~EnginePptx() override;

    EngineBase* Clone() override;
    RectF PageMediabox(int pageNo) override;
    RenderedBitmap* RenderPage(RenderPageArgs& args) override;
    RectF Transform(const RectF& rect, int pageNo, float zoom, int rotation, bool inverse = false) override;
    ByteSlice GetFileData() override;
    bool SaveFileAs(const char* copyFileName) override;
    PageText ExtractPageText(int pageNo) override;
    bool HasClipOptimizations(int) override { return false; }
    TempStr GetPropertyTemp(const char* name) override;
    Vec<IPageElement*> GetElements(int) override { return Vec<IPageElement*>(); }
    IPageElement* GetElementAtPos(int, PointF) override { return nullptr; }
    bool BenchLoadPage(int pageNo) override;

    bool LoadFromFile(const char* path);

  private:
    PptxDoc* doc = nullptr;
    PptxSlide* GetSlide(int pageNo);
    void GetTransform(Matrix& m, int pageNo, float zoom, int rotation);

    // Resolve font name: handle "+mn-lt" / "+mj-lt" theme placeholders
    const char* ResolveFont(const char* fontName) const;
    // Get effective color for a run (resolves -1 via para default, txStyles, then dk1)
    COLORREF EffectiveColor(const PptxTextRun* run, const PptxPara* para, const PptxShape* shape = nullptr) const;
    // Get effective font size for a run (resolves 0 via para default, shape inherited, then 18pt)
    float EffectiveFontSize(const PptxTextRun* run, const PptxPara* para, const PptxShape* shape = nullptr) const;
};

EnginePptx::EnginePptx() {
    kind = kindEnginePptx;
    defaultExt = str::Dup(".pptx");
    preferredLayout.type = PageLayout::Type::Single;
    preferredLayout.nonContinuous = true;
}

EnginePptx::~EnginePptx() {
    delete doc;
}

const char* EnginePptx::ResolveFont(const char* fontName) const {
    if (!fontName || fontName[0] == '\0') {
        // use theme minor (body) font
        if (doc->theme && doc->theme->minorFont && doc->theme->minorFont[0]) {
            return doc->theme->minorFont;
        }
        return "Calibri";
    }
    if (str::Eq(fontName, "+mn-lt") || str::Eq(fontName, "+mn-cs") || str::Eq(fontName, "+mn-ea")) {
        if (doc->theme && doc->theme->minorFont && doc->theme->minorFont[0]) {
            return doc->theme->minorFont;
        }
        return "Calibri";
    }
    if (str::Eq(fontName, "+mj-lt") || str::Eq(fontName, "+mj-cs") || str::Eq(fontName, "+mj-ea")) {
        if (doc->theme && doc->theme->majorFont && doc->theme->majorFont[0]) {
            return doc->theme->majorFont;
        }
        return "Calibri";
    }
    return fontName;
}

COLORREF EnginePptx::EffectiveColor(const PptxTextRun* run, const PptxPara* para, const PptxShape* shape) const {
    if (run->color != (COLORREF)-1) {
        return run->color;
    }
    if (para && para->props.defColor != (COLORREF)-1) {
        return para->props.defColor;
    }
    // Check master text styles for this placeholder type + level
    if (doc->txStyles && shape && shape->phType) {
        int lvl = para ? para->props.lvl : 0;
        const PptxLevelStyle* ls = doc->txStyles->GetLevel(shape->phType, lvl);
        if (ls && ls->color != (COLORREF)-1) {
            return ls->color;
        }
    }
    // Use theme dk1 (usually black/dark text)
    if (doc->theme) {
        return doc->theme->dk1;
    }
    return RGB(0, 0, 0);
}

float EnginePptx::EffectiveFontSize(const PptxTextRun* run, const PptxPara* para, const PptxShape* shape) const {
    if (run->fontSize > 0) {
        return run->fontSize;
    }
    if (para && para->props.defFontSize > 0) {
        return para->props.defFontSize;
    }
    if (shape && shape->phDefFontSize > 0) {
        return shape->phDefFontSize;
    }
    // Check master text styles for this placeholder type + level
    if (doc->txStyles && shape && shape->phType) {
        int lvl = para ? para->props.lvl : 0;
        const PptxLevelStyle* ls = doc->txStyles->GetLevel(shape->phType, lvl);
        if (ls && ls->fontSize > 0) {
            return ls->fontSize;
        }
    }
    // Use sensible defaults based on placeholder type (matches PowerPoint defaults)
    if (shape && shape->phType) {
        if (str::EqI(shape->phType, "title") || str::EqI(shape->phType, "ctrTitle")) {
            return 44.0f;
        }
        if (str::EqI(shape->phType, "subTitle")) {
            return 32.0f;
        }
        if (str::EqI(shape->phType, "body")) {
            // Decrease by outline level
            int lvl = (para ? para->props.lvl : 0);
            float sizes[] = {24.0f, 20.0f, 18.0f, 16.0f, 16.0f};
            return sizes[lvl < 5 ? lvl : 4];
        }
    }
    return 18.0f;
}

bool EnginePptx::LoadFromFile(const char* path) {
    doc = new PptxDoc();
    doc->filePath = str::Dup(path);
    const char* archivePath = path;
    if (str::StartsWith(path, "\\\\?\\")) {
        archivePath = path + 4;
    }
    doc->archive = OpenZipArchive(archivePath, false);
    if (!doc->archive) {
        return false;
    }
    if (!ParsePresentation(doc)) {
        return false;
    }
    pageCount = doc->slidePaths.Size();
    // Pre-size slides vec with nullptrs
    for (int i = 0; i < pageCount; i++) {
        doc->slides.Append(nullptr);
    }
    SetFilePath(path);
    ParseDocProps(doc);
    return true;
}

PptxSlide* EnginePptx::GetSlide(int pageNo) {
    int idx = pageNo - 1;
    if (idx < 0 || idx >= doc->slides.Size()) {
        return nullptr;
    }
    if (!doc->slides[idx]) {
        doc->slides[idx] = ParseSlide(doc->archive, doc->slidePaths[idx], doc->theme);
    }
    return doc->slides[idx];
}

EngineBase* EnginePptx::Clone() {
    EnginePptx* copy = new EnginePptx();
    if (!copy->LoadFromFile(FilePath())) {
        delete copy;
        return nullptr;
    }
    return copy;
}

RectF EnginePptx::PageMediabox(int) {
    float w = EmuToPx(doc->slideCx, 1.0f);
    float h = EmuToPx(doc->slideCy, 1.0f);
    return RectF{0, 0, w, h};
}

void EnginePptx::GetTransform(Matrix& m, int pageNo, float zoom, int rotation) {
    GetBaseTransform(m, ToGdipRectF(PageMediabox(pageNo)), zoom, rotation);
}

RectF EnginePptx::Transform(const RectF& rect, int pageNo, float zoom, int rotation, bool inverse) {
    Gdiplus::PointF pts[2] = {Gdiplus::PointF(rect.x, rect.y), Gdiplus::PointF(rect.x + rect.dx, rect.y + rect.dy)};
    Matrix m;
    GetTransform(m, pageNo, zoom, rotation);
    if (inverse) {
        m.Invert();
    }
    m.TransformPoints(pts, 2);
    RectF res = RectF::FromXY(pts[0].X, pts[0].Y, pts[1].X, pts[1].Y);
    if (rotation != 0) {
        res.Inflate(1, 1);
    }
    return res;
}

ByteSlice EnginePptx::GetFileData() {
    return file::ReadFile(FilePath());
}

bool EnginePptx::SaveFileAs(const char* copyFileName) {
    return file::Copy(copyFileName, FilePath(), false);
}

TempStr EnginePptx::GetPropertyTemp(const char* name) {
    return GetPropValueTemp(doc->props, name);
}

bool EnginePptx::BenchLoadPage(int pageNo) {
    return GetSlide(pageNo) != nullptr;
}

// ===== Rendering =====

RenderedBitmap* EnginePptx::RenderPage(RenderPageArgs& args) {
    int pageNo = args.pageNo;
    float zoom = args.zoom;
    int rotation = args.rotation;
    RectF* pageRect = args.pageRect;

    PptxSlide* slide = GetSlide(pageNo);
    if (!slide) {
        return nullptr;
    }

    RectF pageRc = pageRect ? *pageRect : PageMediabox(pageNo);
    Rect screen = Transform(pageRc, pageNo, zoom, rotation).Round();
    Point screenTL = screen.TL();
    screen.Offset(-screen.x, -screen.y);

    HANDLE hMap = nullptr;
    HBITMAP hbmp = CreateMemoryBitmap(screen.Size(), &hMap);
    if (!hbmp) {
        return nullptr;
    }
    HDC hDC = CreateCompatibleDC(nullptr);
    DeleteObject(SelectObject(hDC, hbmp));

    Graphics g(hDC);
    g.SetInterpolationMode(InterpolationModeHighQualityBicubic);
    g.SetSmoothingMode(SmoothingModeAntiAlias);
    g.SetTextRenderingHint(Gdiplus::TextRenderingHintClearTypeGridFit);
    g.SetPageUnit(UnitPixel);

    Matrix m;
    if (rotation != 0) {
        GetTransform(m, pageNo, zoom, rotation);
        m.Translate((float)-screenTL.x, (float)-screenTL.y, MatrixOrderAppend);
        g.SetTransform(&m);
    } else {
        m.Translate((float)-screenTL.x, (float)-screenTL.y);
        g.SetTransform(&m);
    }

    // --- Background ---
    COLORREF bg = slide->bgColor;
    if (bg == (COLORREF)-1) {
        // Use theme lt1 (usually white)
        bg = (doc->theme) ? doc->theme->lt1 : RGB(255, 255, 255);
    }
    SolidBrush bgBrush(Color(GetRValue(bg), GetGValue(bg), GetBValue(bg)));
    float slideW = EmuToPx(doc->slideCx, zoom);
    float slideH = EmuToPx(doc->slideCy, zoom);
    g.FillRectangle(&bgBrush, Gdiplus::RectF(0, 0, slideW, slideH));

    // Background image (blipFill in <p:bg>)
    if (slide->bgImagePath) {
        ByteSlice bgImgData = doc->archive->GetFileDataByName(slide->bgImagePath);
        if (bgImgData) {
            Gdiplus::RectF fullSlide(0, 0, slideW, slideH);
            if (str::EndsWithI(slide->bgImagePath, ".emf") || str::EndsWithI(slide->bgImagePath, ".wmf")) {
                IStream* strm = CreateStreamFromData(bgImgData);
                if (strm) {
                    Gdiplus::Metafile* mf = new Gdiplus::Metafile(strm);
                    if (mf && mf->GetLastStatus() == Gdiplus::Ok) {
                        g.DrawImage(mf, fullSlide);
                    }
                    delete mf;
                    strm->Release();
                }
            } else {
                Bitmap* bmp = BitmapFromDataWin(bgImgData);
                if (bmp) {
                    g.DrawImage(bmp, fullSlide);
                    delete bmp;
                }
            }
            bgImgData.Free();
        }
    }

    // StringFormat for no-wrap + measure trailing spaces
    StringFormat sfNoWrap;
    sfNoWrap.SetFormatFlags(Gdiplus::StringFormatFlagsNoWrap | Gdiplus::StringFormatFlagsMeasureTrailingSpaces);
    sfNoWrap.SetTrimming(Gdiplus::StringTrimmingNone);

    // --- Draw shapes ---
    for (PptxShape* shape : slide->shapes) {
        float sx = EmuToPx(shape->offX, zoom);
        float sy = EmuToPx(shape->offY, zoom);
        float sw = EmuToPx(shape->extCx, zoom);
        float sh = EmuToPx(shape->extCy, zoom);

        bool isConnector = (shape->type == PptxShapeType::Connector);
        bool hasCustGeom = shape->custPaths.size() > 0;
        // Connectors and custGeom shapes may have zero width or height
        if (!isConnector && !hasCustGeom && (sw <= 0 || sh <= 0)) {
            continue;
        }
        Gdiplus::RectF shapeRect(sx, sy, sw, sh);

        // Declare preset geometry state here so goto render_text doesn't skip initialization
        bool hasPrstGeom = false;
        Gdiplus::GraphicsPath prstPath;

        // Apply per-shape rotation / flip around the shape centre
        // Connectors handle flip manually via endpoint swap — skip matrix transform to avoid double-flip
        bool hasTransform = (shape->rot != 0 || shape->flipH || shape->flipV);
        if (isConnector) {
            hasTransform = false;
        }
        Matrix savedMat;
        if (hasTransform) {
            g.GetTransform(&savedMat);
            float cx = sx + sw / 2.0f;
            float cy = sy + sh / 2.0f;
            // Order (MatrixOrderAppend = post-multiply onto world transform):
            //   translate center to origin → flip → rotate → translate back
            g.TranslateTransform(-cx, -cy, MatrixOrderAppend);
            if (shape->flipH || shape->flipV) {
                float scaleX = shape->flipH ? -1.0f : 1.0f;
                float scaleY = shape->flipV ? -1.0f : 1.0f;
                g.ScaleTransform(scaleX, scaleY, MatrixOrderAppend);
            }
            if (shape->rot != 0) {
                float deg = (float)shape->rot / 60000.0f;
                g.RotateTransform(deg, MatrixOrderAppend);
            }
            g.TranslateTransform(cx, cy, MatrixOrderAppend);
        }

        // Connector: render as a single line segment
        if (isConnector) {
            COLORREF lc = (shape->borderColor != (COLORREF)-1) ? shape->borderColor
                                                               : (doc->theme ? doc->theme->dk1 : RGB(0, 0, 0));
            float lw = (shape->borderWidth > 0) ? EmuToPx((i64)shape->borderWidth, zoom) : 1.0f;
            if (lw < 0.5f) {
                lw = 0.5f;
            }
            if (!shape->noBorder) {
                Pen connPen(Color(GetRValue(lc), GetGValue(lc), GetBValue(lc)), lw);
                // Diagonal direction controlled by flip flags
                float x1 = sx, y1 = sy, x2 = sx + sw, y2 = sy + sh;
                if (shape->flipH) {
                    x1 = sx + sw;
                    x2 = sx;
                }
                if (shape->flipV) {
                    y1 = sy + sh;
                    y2 = sy;
                }
                g.DrawLine(&connPen, x1, y1, x2, y2);
            }
            if (hasTransform) {
                g.SetTransform(&savedMat);
            }
            continue;
        }

        // Custom geometry paths — render via GraphicsPath instead of rect fill
        if (hasCustGeom) {
            // Effective shape dimensions for scaling (at least 1 to avoid div-by-zero)
            float shapePxW = (sw > 0) ? sw : 1.0f;
            float shapePxH = (sh > 0) ? sh : 1.0f;

            for (PptxCustPath* cp : shape->custPaths) {
                float pathW = (cp->w > 0) ? (float)cp->w : (float)shape->extCx;
                float pathH = (cp->h > 0) ? (float)cp->h : (float)shape->extCy;
                if (pathW <= 0) {
                    pathW = 1.0f;
                }
                if (pathH <= 0) {
                    pathH = 1.0f;
                }
                float scaleX = shapePxW / pathW;
                float scaleY = shapePxH / pathH;

                Gdiplus::GraphicsPath gp;
                float curPtX = sx, curPtY = sy;
                bool hasMove = false;
                for (const PptxPathCmd& cmd : cp->cmds) {
                    float px = sx + cmd.pt.x * scaleX;
                    float py = sy + cmd.pt.y * scaleY;
                    if (cmd.type == PptxPathCmdType::MoveTo) {
                        gp.StartFigure();
                        curPtX = px;
                        curPtY = py;
                        hasMove = true;
                    } else if (cmd.type == PptxPathCmdType::LineTo && hasMove) {
                        gp.AddLine(curPtX, curPtY, px, py);
                        curPtX = px;
                        curPtY = py;
                    } else if (cmd.type == PptxPathCmdType::Close) {
                        gp.CloseFigure();
                        hasMove = false;
                    }
                }

                if (shape->fillColor != (COLORREF)-1) {
                    COLORREF fc = shape->fillColor;
                    SolidBrush fb(Color(GetRValue(fc), GetGValue(fc), GetBValue(fc)));
                    g.FillPath(&fb, &gp);
                }
                if (!shape->noBorder) {
                    COLORREF lc = (shape->borderColor != (COLORREF)-1) ? shape->borderColor
                                                                       : (doc->theme ? doc->theme->dk1 : RGB(0, 0, 0));
                    float lw = (shape->borderWidth > 0) ? EmuToPx((i64)shape->borderWidth, zoom) : 0.0f;
                    if (lw > 0.0f) {
                        if (lw < 0.5f) {
                            lw = 0.5f;
                        }
                        Pen lp(Color(GetRValue(lc), GetGValue(lc), GetBValue(lc)), lw);
                        g.DrawPath(&lp, &gp);
                    }
                }
            }
            // Still render text on top if present
            if (shape->paras.IsEmpty()) {
                if (hasTransform) {
                    g.SetTransform(&savedMat);
                }
                continue;
            }
            // Fall through to text rendering below (skip rect fill)
            goto render_text;
        }

        // Preset geometry: build a GraphicsPath for the shape outline
        hasPrstGeom = (shape->prstGeom != nullptr);
        if (hasPrstGeom) {
            const char* prst = shape->prstGeom;
            if (str::EqI(prst, "ellipse") || str::EqI(prst, "oval")) {
                prstPath.AddEllipse(shapeRect);
            } else if (str::EqI(prst, "roundRect") || str::EqI(prst, "round2SameRect") ||
                       str::EqI(prst, "snipRoundRect")) {
                float radius = (sw < sh ? sw : sh) * 0.166f; // ~1/6 of smaller dimension
                float d = radius * 2;
                prstPath.AddArc(sx, sy, d, d, 180, 90);
                prstPath.AddArc(sx + sw - d, sy, d, d, 270, 90);
                prstPath.AddArc(sx + sw - d, sy + sh - d, d, d, 0, 90);
                prstPath.AddArc(sx, sy + sh - d, d, d, 90, 90);
                prstPath.CloseFigure();
            } else if (str::EqI(prst, "triangle") || str::EqI(prst, "rtTriangle")) {
                Gdiplus::PointF pts3[3] = {{sx + sw / 2, sy}, {sx + sw, sy + sh}, {sx, sy + sh}};
                prstPath.AddPolygon(pts3, 3);
            } else if (str::EqI(prst, "diamond")) {
                Gdiplus::PointF pts4[4] = {
                    {sx + sw / 2, sy}, {sx + sw, sy + sh / 2}, {sx + sw / 2, sy + sh}, {sx, sy + sh / 2}};
                prstPath.AddPolygon(pts4, 4);
            } else if (str::EqI(prst, "hexagon")) {
                float qw = sw * 0.25f;
                Gdiplus::PointF pts6[6] = {{sx + qw, sy},           {sx + sw - qw, sy}, {sx + sw, sy + sh / 2},
                                           {sx + sw - qw, sy + sh}, {sx + qw, sy + sh}, {sx, sy + sh / 2}};
                prstPath.AddPolygon(pts6, 6);
            } else if (str::EqI(prst, "parallelogram")) {
                float off = sw * 0.2f;
                Gdiplus::PointF pts4p[4] = {{sx + off, sy}, {sx + sw, sy}, {sx + sw - off, sy + sh}, {sx, sy + sh}};
                prstPath.AddPolygon(pts4p, 4);
            } else if (str::EqI(prst, "trapezoid")) {
                float off = sw * 0.2f;
                Gdiplus::PointF pts4t[4] = {{sx + off, sy}, {sx + sw - off, sy}, {sx + sw, sy + sh}, {sx, sy + sh}};
                prstPath.AddPolygon(pts4t, 4);
            } else if (str::EqI(prst, "pentagon")) {
                float mid = sw / 2;
                Gdiplus::PointF pts5[5] = {{sx + mid, sy},
                                           {sx + sw, sy + sh * 0.38f},
                                           {sx + sw * 0.81f, sy + sh},
                                           {sx + sw * 0.19f, sy + sh},
                                           {sx, sy + sh * 0.38f}};
                prstPath.AddPolygon(pts5, 5);
            } else if (str::EqI(prst, "rightArrow") || str::EqI(prst, "leftArrow") || str::EqI(prst, "upArrow") ||
                       str::EqI(prst, "downArrow")) {
                // Simple arrow as a polygon
                float qh = sh * 0.25f;
                float hw = sw * 0.6f;
                if (str::EqI(prst, "rightArrow")) {
                    Gdiplus::PointF pa[7] = {{sx, sy + qh},          {sx + hw, sy + qh}, {sx + hw, sy},
                                             {sx + sw, sy + sh / 2}, {sx + hw, sy + sh}, {sx + hw, sy + sh - qh},
                                             {sx, sy + sh - qh}};
                    prstPath.AddPolygon(pa, 7);
                } else if (str::EqI(prst, "leftArrow")) {
                    Gdiplus::PointF pa[7] = {{sx + sw, sy + qh},      {sx + sw - hw, sy + qh},
                                             {sx + sw - hw, sy},      {sx, sy + sh / 2},
                                             {sx + sw - hw, sy + sh}, {sx + sw - hw, sy + sh - qh},
                                             {sx + sw, sy + sh - qh}};
                    prstPath.AddPolygon(pa, 7);
                } else {
                    // up/down arrows — just use rect approximation
                    prstPath.AddRectangle(shapeRect);
                }
            } else if (str::EqI(prst, "star5") || str::EqI(prst, "star4") || str::EqI(prst, "star6")) {
                // Approximate as ellipse
                prstPath.AddEllipse(shapeRect);
            } else {
                // Unknown preset — fall back to rectangle
                hasPrstGeom = false;
            }
        }

        // Solid fill
        if (shape->fillColor != (COLORREF)-1) {
            COLORREF fc = shape->fillColor;
            SolidBrush fillBrush(Color(GetRValue(fc), GetGValue(fc), GetBValue(fc)));
            if (hasPrstGeom) {
                g.FillPath(&fillBrush, &prstPath);
            } else {
                g.FillRectangle(&fillBrush, shapeRect);
            }
        }

        // Image — draw whenever imagePath is set (handles both <p:pic> and
        // <p:sp> shapes whose spPr has a <a:blipFill>).
        if (shape->imagePath) {
            ByteSlice imgData = doc->archive->GetFileDataByName(shape->imagePath);
            if (imgData) {
                bool drawn = false;
                // EMF/WMF are vector metafiles — load via Gdiplus::Metafile
                if (str::EndsWithI(shape->imagePath, ".emf") || str::EndsWithI(shape->imagePath, ".wmf")) {
                    IStream* strm = CreateStreamFromData(imgData);
                    if (strm) {
                        Gdiplus::Metafile* mf = new Gdiplus::Metafile(strm);
                        if (mf && mf->GetLastStatus() == Gdiplus::Ok) {
                            g.DrawImage(mf, shapeRect);
                            drawn = true;
                        }
                        delete mf;
                        strm->Release();
                    }
                }
                if (!drawn) {
                    Bitmap* bmp = BitmapFromDataWin(imgData);
                    if (bmp) {
                        g.DrawImage(bmp, shapeRect);
                        delete bmp;
                    }
                }
                imgData.Free();
            }
            // Pure image shape (<p:pic>) — draw border if set, then done.
            if (shape->type == PptxShapeType::Image) {
                if (!shape->noBorder && shape->borderWidth > 0 && shape->borderColor != (COLORREF)-1) {
                    float bw = EmuToPx((i64)shape->borderWidth, zoom);
                    if (bw < 0.5f) {
                        bw = 0.5f;
                    }
                    COLORREF bc = shape->borderColor;
                    Pen bp(Color(GetRValue(bc), GetGValue(bc), GetBValue(bc)), bw);
                    g.DrawRectangle(&bp, shapeRect);
                }
                if (hasTransform) {
                    g.SetTransform(&savedMat);
                }
                continue;
            }
            // Image-fill text shape — fall through to render text on top.
        }

        // Border / outline for non-image shapes
        if (!shape->noBorder && shape->borderWidth > 0 && shape->borderColor != (COLORREF)-1) {
            float bw = EmuToPx((i64)shape->borderWidth, zoom);
            if (bw < 0.5f) {
                bw = 0.5f;
            }
            COLORREF bc = shape->borderColor;
            Pen bp(Color(GetRValue(bc), GetGValue(bc), GetBValue(bc)), bw);
            if (hasPrstGeom) {
                g.DrawPath(&bp, &prstPath);
            } else {
                g.DrawRectangle(&bp, shapeRect);
            }
        }

        if (shape->type != PptxShapeType::Text) {
            if (hasTransform) {
                g.SetTransform(&savedMat);
            }
            continue;
        }

    render_text:
        // --- Text rendering ---
        const PptxBodyProps& bp = shape->bodyProps;

        // Font scale from normAutofit (e.g. 80% means text shrinks to fit)
        float fontScaleMul = 1.0f;
        if (bp.fontScale > 0.0f && bp.fontScale < 100.0f) {
            fontScaleMul = bp.fontScale / 100.0f;
        }

        // Vertical text (vert="vert"): rotate 90° CW around shape center and swap w/h.
        // Only apply rotation for portrait shapes (taller than wide); landscape vert shapes
        // render better with normal horizontal layout (e.g. short column header boxes).
        if (bp.vert && sh > sw) {
            if (!hasTransform) {
                g.GetTransform(&savedMat);
                hasTransform = true;
            }
            float vcx = sx + sw / 2.0f, vcy = sy + sh / 2.0f;
            g.TranslateTransform(-vcx, -vcy, MatrixOrderAppend);
            g.RotateTransform(90.0f, MatrixOrderAppend);
            g.TranslateTransform(vcx, vcy, MatrixOrderAppend);
            // After rotation the logical text rect has swapped dimensions
            float tmp = sw;
            sw = sh;
            sh = tmp;
            sx = vcx - sw / 2.0f;
            sy = vcy - sh / 2.0f;
        }

        float lIns = EmuToPx(bp.lIns, zoom);
        float tIns = EmuToPx(bp.tIns, zoom);
        float rIns = EmuToPx(bp.rIns, zoom);
        float bIns = EmuToPx(bp.bIns, zoom);

        // Text area within the shape (after insets)
        float tx = sx + lIns;
        float ty = sy + tIns;
        float tw = sw - lIns - rIns;
        float th = sh - tIns - bIns;
        if (tw <= 0 || th <= 0) {
            continue;
        }

        // First pass: compute total text height for vertical anchoring
        // We'll do a quick measurement pass
        float totalTextH = 0.0f;
        if (bp.anchor != 0) {
            for (PptxPara* para : shape->paras) {
                float paraLineH = 0.0f;
                for (PptxTextRun* run : para->runs) {
                    if (!run->text || !*run->text) {
                        continue;
                    }
                    float fs = EffectiveFontSize(run, para, shape) * fontScaleMul * zoom;
                    int style = (run->bold || para->props.defBold ? FontStyleBold : FontStyleRegular) |
                                (run->italic || para->props.defItalic ? FontStyleItalic : 0);
                    TempWStr fn = ToWStrTemp(ResolveFont(run->fontName));
                    Font font(fn ? fn : L"Calibri", PtToPx(fs), style, UnitPixel);
                    Gdiplus::RectF box;
                    g.MeasureString(L"Mg", -1, &font, Gdiplus::RectF(0, 0, 9999, 9999), &sfNoWrap, &box);
                    if (box.Height > paraLineH) {
                        paraLineH = box.Height;
                    }
                }
                if (paraLineH == 0.0f) {
                    paraLineH = 12.0f * zoom * (96.0f / 72.0f);
                }
                float lineHSp;
                if (para->props.lnSpcPts > 0) {
                    lineHSp = para->props.lnSpcPts * zoom * (96.0f / 72.0f);
                } else {
                    float lnMul2 = (para->props.lnSpcPct > 0) ? (para->props.lnSpcPct / 100.0f) : 1.15f;
                    lineHSp = paraLineH * lnMul2;
                }
                totalTextH += lineHSp;
                if (para->props.spcBefPt > 0) {
                    totalTextH += para->props.spcBefPt * zoom * (96.0f / 72.0f);
                } else if (para->props.spcBefPct > 0) {
                    totalTextH += lineHSp * para->props.spcBefPct / 100.0f;
                }
                if (para->props.spcAftPt > 0) {
                    totalTextH += para->props.spcAftPt * zoom * (96.0f / 72.0f);
                } else if (para->props.spcAftPct > 0) {
                    totalTextH += lineHSp * para->props.spcAftPct / 100.0f;
                }
            }
        }

        // Compute starting Y based on vertical anchor
        float lineY = ty;
        if (bp.anchor == 1) { // center
            float offset = (th - totalTextH) / 2.0f;
            if (offset > 0) {
                lineY = ty + offset;
            }
        } else if (bp.anchor == 2) { // bottom
            float offset = th - totalTextH;
            if (offset > 0) {
                lineY = ty + offset;
            }
        }

        float shapeRight = tx + tw;
        float shapeBottom = sy + sh - bIns;

        int autoBulletNum = 1; // counter per shape for auto-numbered lists

        for (PptxPara* para : shape->paras) {
            const PptxParaProps& pp = para->props;

            // spcBefPct is handled after paraLineH is computed (needs line height)

            // Compute line height for this paragraph
            float paraLineH = 0.0f;
            float defFs = 12.0f * fontScaleMul * zoom;
            for (PptxTextRun* run : para->runs) {
                if (!run->text || !*run->text) {
                    continue;
                }
                float fs = EffectiveFontSize(run, para, shape) * fontScaleMul * zoom;
                if (fs > defFs) {
                    defFs = fs;
                }
                int style = ((run->bold || pp.defBold) ? FontStyleBold : FontStyleRegular) |
                            ((run->italic || pp.defItalic) ? FontStyleItalic : 0);
                TempWStr fn2 = ToWStrTemp(ResolveFont(run->fontName));
                Font font(fn2 ? fn2 : L"Calibri", PtToPx(fs), style, UnitPixel);
                Gdiplus::RectF box;
                g.MeasureString(L"Mg", -1, &font, Gdiplus::RectF(0, 0, 9999, 9999), &sfNoWrap, &box);
                if (box.Height > paraLineH) {
                    paraLineH = box.Height;
                }
            }
            if (paraLineH == 0.0f) {
                // Empty paragraph: use default/inherited size
                float fs = (pp.defFontSize > 0 ? pp.defFontSize : 12.0f) * fontScaleMul * zoom;
                TempWStr efn = ToWStrTemp(ResolveFont(nullptr));
                Font ef(efn ? efn : L"Calibri", PtToPx(fs), FontStyleRegular, UnitPixel);
                Gdiplus::RectF box;
                g.MeasureString(L"Mg", -1, &ef, Gdiplus::RectF(0, 0, 9999, 9999), &sfNoWrap, &box);
                paraLineH = box.Height > 0 ? box.Height : fs * (96.0f / 72.0f);
                lineY += paraLineH;
                continue;
            }

            float lineHSpaced;
            if (pp.lnSpcPts > 0) {
                lineHSpaced = pp.lnSpcPts * zoom * (96.0f / 72.0f);
            } else {
                float lnMul = (pp.lnSpcPct > 0) ? (pp.lnSpcPct / 100.0f) : 1.15f;
                // Apply lnSpcReduction from normAutofit
                if (bp.lnSpcReduction > 0.0f) {
                    lnMul = lnMul * (1.0f - bp.lnSpcReduction / 100.0f);
                    if (lnMul < 0.5f) {
                        lnMul = 0.5f;
                    }
                }
                lineHSpaced = paraLineH * lnMul;
            }

            // Space before paragraph (deferred to after lineH computation)
            if (pp.spcBefPt > 0) {
                lineY += pp.spcBefPt * zoom * (96.0f / 72.0f);
            } else if (pp.spcBefPct > 0) {
                lineY += lineHSpaced * pp.spcBefPct / 100.0f;
            }

            if (lineY >= shapeBottom) {
                break;
            }

            // Check txStyles for inherited bullet/margin if not explicitly set
            const PptxLevelStyle* txLvl = nullptr;
            if (doc->txStyles && shape->phType) {
                txLvl = doc->txStyles->GetLevel(shape->phType, pp.lvl);
            }

            // Determine effective bullet state: explicit pPr > txStyles > default
            bool effHasBullet = pp.hasBullet;
            bool effBulletIsNone = pp.bulletIsNone;
            const char* effBulletChar = pp.bulletCharStr;
            const char* effBulletFont = pp.buFontName;
            COLORREF effBulletColor = pp.buColor;
            if (!pp.hasBullet && !pp.bulletIsNone && txLvl) {
                effHasBullet = txLvl->hasBullet;
                effBulletIsNone = txLvl->bulletIsNone;
                if (!effBulletChar && txLvl->bulletChar) {
                    effBulletChar = txLvl->bulletChar;
                }
                if (!effBulletFont && txLvl->bulletFont) {
                    effBulletFont = txLvl->bulletFont;
                }
                if (effBulletColor == (COLORREF)-1 && txLvl->bulletColor != (COLORREF)-1) {
                    effBulletColor = txLvl->bulletColor;
                }
            }

            // Left margin / indent from para props, then txStyles
            float paraMarL;
            if (pp.marL >= 0) {
                paraMarL = EmuToPx(pp.marL, zoom);
            } else if (txLvl && txLvl->marL >= 0) {
                paraMarL = EmuToPx(txLvl->marL, zoom);
            } else if (effHasBullet && !effBulletIsNone) {
                // Default bullet indent ~0.5" per level (matches PowerPoint defaults)
                i64 defaultMarL = (i64)(pp.lvl + 1) * 457200;
                paraMarL = EmuToPx(defaultMarL, zoom);
            } else {
                paraMarL = 0.0f;
            }
            // Bullet indent: use marL as hanging indent base
            float bulletIndent = paraMarL;
            float textStartX = tx + bulletIndent;

            // --- Draw bullet ---
            if (effHasBullet && !effBulletIsNone) {
                // Bullet color: explicit buClr > defColor > txStyle > theme dk1
                COLORREF bulletColor;
                if (effBulletColor != (COLORREF)-1) {
                    bulletColor = effBulletColor;
                } else if (pp.defColor != (COLORREF)-1) {
                    bulletColor = pp.defColor;
                } else {
                    bulletColor = doc->theme ? doc->theme->dk1 : RGB(0, 0, 0);
                }

                // Bullet font size: buSzPts > buSzPct > txStyle buSzPct > same as text
                float bFs = defFs;
                if (pp.buSzPts > 0) {
                    bFs = pp.buSzPts * fontScaleMul * zoom;
                } else if (pp.buSzPct > 0) {
                    bFs = defFs * pp.buSzPct / 100.0f;
                } else if (txLvl && txLvl->bulletSzPct > 0) {
                    bFs = defFs * txLvl->bulletSzPct / 100.0f;
                }

                // Bullet font: explicit buFont > txStyle buFont > text font
                const char* bFontU8 = effBulletFont ? ResolveFont(effBulletFont) : ResolveFont(nullptr);
                TempWStr bfn = ToWStrTemp(bFontU8);
                Font bFont(bfn ? bfn : L"Calibri", PtToPx(bFs), FontStyleRegular, UnitPixel);
                SolidBrush bBrush(Color(GetRValue(bulletColor), GetGValue(bulletColor), GetBValue(bulletColor)));

                char bulletBuf[32] = {0};
                if (pp.bulletAutoNum) {
                    str::BufFmt(bulletBuf, sizeof(bulletBuf), "%d.", autoBulletNum++);
                } else if (effBulletChar) {
                    str::BufFmt(bulletBuf, sizeof(bulletBuf), "%s", effBulletChar);
                } else {
                    bulletBuf[0] = '\xe2';
                    bulletBuf[1] = '\x80';
                    bulletBuf[2] = '\xa2'; // • U+2022
                    bulletBuf[3] = 0;
                }
                TempWStr wBullet = ToWStrTemp(bulletBuf);
                if (wBullet) {
                    // Draw bullet to left of text
                    Gdiplus::RectF bBox;
                    g.MeasureString(wBullet, -1, &bFont, Gdiplus::RectF(0, 0, 9999, 9999), &sfNoWrap, &bBox);
                    float bx = tx + paraMarL - bBox.Width - EmuToPx(114300, zoom); // small gap
                    if (bx < tx) {
                        bx = tx;
                    }
                    Gdiplus::RectF bDrawRect(bx, lineY, bBox.Width + 4, paraLineH);
                    g.DrawString(wBullet, -1, &bFont, bDrawRect, &sfNoWrap, &bBrush);
                }
            }

            // --- Draw runs, with word-wrap and alignment ---
            // Strategy: collect all (token, font, color, width) tuples for the
            // paragraph, then lay them out line-by-line respecting alignment.

            struct TokInfo {
                const wchar_t* start;
                int len;
                float width;
                Font* font;
                COLORREF color;
                bool isSpace;   // trailing-space-only token (used for wrapping)
                bool isNewline; // forced line break (from <a:br/>)
                float spcPx;    // per-character spacing adjustment in pixels (from run->spc)
            };
            Vec<TokInfo> toks;
            // Keep Font objects alive for the duration of the paragraph draw
            Vec<Font*> paraFonts;

            for (PptxTextRun* run : para->runs) {
                if (!run->text || !*run->text) {
                    continue;
                }
                float fs = EffectiveFontSize(run, para, shape) * fontScaleMul * zoom;
                int style = FontStyleRegular;
                // Bold: explicit run > para default > shape inherited > txStyles
                bool isBold = run->bold || pp.defBold || shape->phDefBold;
                if (!isBold && txLvl && txLvl->bold) {
                    isBold = true;
                }
                if (isBold) {
                    style |= FontStyleBold;
                }
                bool isItalic = run->italic || pp.defItalic;
                if (!isItalic && txLvl && txLvl->italic) {
                    isItalic = true;
                }
                if (isItalic) {
                    style |= FontStyleItalic;
                }
                if (run->underline) {
                    style |= FontStyleUnderline;
                }
                if (run->strikethrough) {
                    style |= FontStyleStrikeout;
                }
                // Font name: explicit run > para default > txStyles > theme
                const char* fontNameU8 = run->fontName;
                if (!fontNameU8 && pp.defFont) {
                    fontNameU8 = pp.defFont;
                }
                if (!fontNameU8 && txLvl && txLvl->fontName) {
                    fontNameU8 = txLvl->fontName;
                }
                fontNameU8 = ResolveFont(fontNameU8);
                TempWStr fontNameW = ToWStrTemp(fontNameU8);
                const wchar_t* fontW = fontNameW ? fontNameW : L"Calibri";
                Font* font = new Font(fontW, PtToPx(fs), style, UnitPixel);
                paraFonts.Append(font);
                COLORREF rc = EffectiveColor(run, para, shape);

                TempWStr wtext = ToWStrTemp(run->text);
                if (!wtext) {
                    continue;
                }
                // spc: per-character spacing in hundredths of a point
                float spcPx = 0.0f;
                if (run->spc != INT_MIN) {
                    spcPx = run->spc / 100.0f * zoom * (96.0f / 72.0f);
                }
                // Split into word+space tokens, treating newlines as forced breaks
                const wchar_t* p = wtext;
                while (*p) {
                    // Handle newline as a forced line break token
                    if (*p == L'\n') {
                        TokInfo ti;
                        ti.start = p;
                        ti.len = 0;
                        ti.width = 0;
                        ti.font = font;
                        ti.color = rc;
                        ti.isSpace = false;
                        ti.isNewline = true;
                        ti.spcPx = 0;
                        toks.Append(ti);
                        p++;
                        continue;
                    }
                    const wchar_t* tokStart = p;
                    while (*p && *p != L' ' && *p != L'\t' && *p != L'\n') {
                        p++;
                    }
                    while (*p == L' ' || *p == L'\t') {
                        p++;
                    }
                    int tokLen = (int)(p - tokStart);
                    if (tokLen == 0) {
                        break;
                    }
                    Gdiplus::RectF box;
                    g.MeasureString(tokStart, tokLen, font, Gdiplus::RectF(0, 0, 9999, 9999), &sfNoWrap, &box);
                    TokInfo ti;
                    ti.start = tokStart;
                    ti.len = tokLen;
                    ti.width = box.Width + spcPx * tokLen;
                    ti.font = font;
                    ti.color = rc;
                    ti.isSpace = false;
                    ti.isNewline = false;
                    ti.spcPx = spcPx;
                    toks.Append(ti);
                }
            }

            // Lay out tokens into visual lines, then draw with alignment
            int t = 0;
            int nToks = toks.Size();
            bool doneEarly = false;
            StringFormat sfDraw;
            sfDraw.SetFormatFlags(Gdiplus::StringFormatFlagsNoWrap | Gdiplus::StringFormatFlagsMeasureTrailingSpaces);
            sfDraw.SetTrimming(Gdiplus::StringTrimmingNone);

            while (t < nToks && !doneEarly) {
                // Greedy: collect tokens for this visual line
                float lineW = 0;
                int lineStart = t;
                while (t < nToks) {
                    // Forced line break token
                    if (toks[t].isNewline) {
                        t++; // consume the newline token
                        break;
                    }
                    float nextW = toks[t].width;
                    if (t > lineStart && lineW + nextW > (shapeRight - textStartX) + 1.0f) {
                        break; // wrap here
                    }
                    lineW += nextW;
                    t++;
                }
                if (t == lineStart) {
                    // single token wider than line — draw it anyway to avoid infinite loop
                    t++;
                    lineW = toks[lineStart].width;
                }

                // Compute starting X for this visual line based on alignment
                float startX = textStartX;
                if (pp.algn == 1) { // center
                    float space = (shapeRight - textStartX) - lineW;
                    startX = textStartX + (space > 0 ? space / 2.0f : 0.0f);
                } else if (pp.algn == 2) { // right
                    startX = shapeRight - lineW;
                    if (startX < textStartX) {
                        startX = textStartX;
                    }
                }

                // Draw tokens in this line
                float runX = startX;
                for (int i = lineStart; i < t; i++) {
                    const TokInfo& ti = toks[i];
                    SolidBrush brush(Color(GetRValue(ti.color), GetGValue(ti.color), GetBValue(ti.color)));
                    float availW = shapeRight - runX;
                    if (availW <= 0) {
                        break;
                    }
                    Gdiplus::RectF drawRect(runX, lineY, availW, paraLineH);
                    g.DrawString(ti.start, ti.len, ti.font, drawRect, &sfDraw, &brush);
                    runX += ti.width;
                }

                // Advance line unless this was the last line in the paragraph
                if (t < nToks) {
                    lineY += lineHSpaced;
                    if (lineY >= shapeBottom) {
                        doneEarly = true;
                    }
                }
            }

            // Free font objects
            for (Font* f : paraFonts) {
                delete f;
            }

            lineY += lineHSpaced;

            // Space after paragraph
            if (pp.spcAftPt > 0) {
                lineY += pp.spcAftPt * zoom * (96.0f / 72.0f);
            } else if (pp.spcAftPct > 0) {
                lineY += lineHSpaced * pp.spcAftPct / 100.0f;
            }
        }

        // Restore per-shape transform
        if (hasTransform) {
            g.SetTransform(&savedMat);
        }
    }

    DeleteDC(hDC);
    return new RenderedBitmap(hbmp, screen.Size(), hMap);
}

// ===== Text Extraction =====

PageText EnginePptx::ExtractPageText(int pageNo) {
    PptxSlide* slide = GetSlide(pageNo);
    if (!slide) {
        return {};
    }

    Vec<WCHAR> textBuf;
    Vec<Rect> coordBuf;

    for (PptxShape* shape : slide->shapes) {
        if (shape->type != PptxShapeType::Text) {
            continue;
        }
        float shapeX = EmuToPx(shape->offX, 1.0f);
        float shapeY = EmuToPx(shape->offY, 1.0f);
        float shapeW = EmuToPx(shape->extCx, 1.0f);
        const PptxBodyProps& bp = shape->bodyProps;
        float lIns = EmuToPx(bp.lIns, 1.0f);
        float tIns = EmuToPx(bp.tIns, 1.0f);
        float tx = shapeX + lIns;
        float ty = shapeY + tIns;

        float lineY = ty;
        for (PptxPara* para : shape->paras) {
            float fs = (para->props.defFontSize > 0 ? para->props.defFontSize : 18.0f);
            float charH = fs * (96.0f / 72.0f) * 1.2f;
            float charW = fs * (96.0f / 72.0f) * 0.55f;
            float runX = tx;
            for (PptxTextRun* run : para->runs) {
                if (!run->text || !*run->text) {
                    continue;
                }
                float rFs = EffectiveFontSize(run, para, shape);
                float rW = rFs * (96.0f / 72.0f) * 0.55f;
                float rH = rFs * (96.0f / 72.0f) * 1.2f;
                TempWStr wt = ToWStrTemp(run->text);
                if (!wt) {
                    continue;
                }
                for (const wchar_t* ch = wt; *ch; ch++) {
                    if (runX + rW > shapeX + shapeW) {
                        runX = tx;
                        lineY += rH;
                    }
                    textBuf.Append(*ch);
                    Rect r((int)runX, (int)lineY, (int)rW, (int)rH);
                    coordBuf.Append(r);
                    runX += rW;
                }
            }
            textBuf.Append('\n');
            coordBuf.Append(Rect(0, 0, 0, 0));
            lineY += charH;
        }
    }

    if (textBuf.IsEmpty()) {
        return {};
    }

    size_t len = textBuf.Size();
    WCHAR* text = AllocArray<WCHAR>(len + 1);
    memcpy(text, textBuf.LendData(), len * sizeof(WCHAR));
    text[len] = 0;

    Rect* coords = AllocArray<Rect>(len + 1);
    memcpy(coords, coordBuf.LendData(), len * sizeof(Rect));

    PageText pt;
    pt.text = text;
    pt.coords = coords;
    pt.len = (int)len;
    return pt;
}

// ===== PPTX → PDF conversion (LibreOffice / PowerPoint) =====

// Returns path to soffice.exe, or nullptr if LibreOffice is not installed.
static const char* FindLibreOfficePath() {
    static const char* kCandidates[] = {
        "C:\\Program Files\\LibreOffice\\program\\soffice.exe",
        "C:\\Program Files (x86)\\LibreOffice\\program\\soffice.exe",
        "C:\\Program Files\\LibreOffice 25\\program\\soffice.exe",
        "C:\\Program Files\\LibreOffice 24\\program\\soffice.exe",
        "C:\\Program Files\\LibreOffice 7\\program\\soffice.exe",
        "C:\\Program Files (x86)\\LibreOffice 7\\program\\soffice.exe",
        nullptr,
    };
    for (int i = 0; kCandidates[i]; i++) {
        if (file::Exists(kCandidates[i])) {
            return kCandidates[i];
        }
    }
    return nullptr;
}

// Build a stable cache path in %TEMP% keyed on pptxPath + modification time.
// Returns heap-allocated string (caller should wrap in AutoFreeStr).
static char* BuildPptxCachePdfPath(const char* pptxPath) {
    FILETIME ft = file::GetModificationTime(pptxPath);
    uint64_t mtime = ((uint64_t)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    u32 h = MurmurHashStrI(pptxPath) ^ (u32)(mtime >> 32) ^ (u32)mtime;

    WCHAR tempDirW[MAX_PATH];
    GetTempPathW(MAX_PATH, tempDirW);
    TempStr tempDir = ToUtf8Temp(tempDirW);
    return str::Format("%s\\sumatrapptx_%08x.pdf", tempDir, h);
}

// Spawn LibreOffice headless to convert pptxPath → outPdf.
// LibreOffice writes <basename>.pdf into outDir; we then rename it to outPdf.
static bool ConvertPptxViaLibreOffice(const char* sofficePath, const char* pptxPath, const char* outPdf) {
    WCHAR tempDirW[MAX_PATH];
    GetTempPathW(MAX_PATH, tempDirW);
    TempStr tempDir = ToUtf8Temp(tempDirW);

    // Build command line
    AutoFreeStr cmd(
        str::Format("\"%s\" --headless --convert-to pdf --outdir \"%s\" \"%s\"", sofficePath, tempDir, pptxPath));
    TempWStr cmdW = ToWStrTemp(cmd.Get());

    STARTUPINFOW si = {};
    si.cb = sizeof(si);
    PROCESS_INFORMATION pi = {};

    BOOL ok = CreateProcessW(nullptr, cmdW, nullptr, nullptr, FALSE, CREATE_NO_WINDOW, nullptr, nullptr, &si, &pi);
    if (!ok) {
        return false;
    }
    // Wait up to 120 seconds for conversion
    WaitForSingleObject(pi.hProcess, 120000);
    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);

    // LibreOffice names the output <basename_noext>.pdf in tempDir
    TempStr basename = path::GetBaseNameTemp(pptxPath);
    TempStr noExt = path::GetPathNoExtTemp(basename);
    AutoFreeStr loOut(str::Format("%s\\%s.pdf", tempDir, noExt));

    if (!file::Exists(loOut)) {
        return false;
    }

    // Move into our stable cache location
    TempWStr srcW = ToWStrTemp(loOut.Get());
    TempWStr dstW = ToWStrTemp(outPdf);
    MoveFileExW(srcW, dstW, MOVEFILE_REPLACE_EXISTING);
    return file::Exists(outPdf);
}

// Try to convert pptxPath to PDF using PowerPoint COM automation.
// Returns heap-allocated PDF path on success, nullptr otherwise.
static char* ConvertPptxViaPowerPoint(const char* pptxPath) {
    // PowerPoint.Application ProgID CLSID
    CLSID clsid;
    if (FAILED(CLSIDFromProgID(L"PowerPoint.Application", &clsid))) {
        return nullptr;
    }

    IDispatch* pApp = nullptr;
    HRESULT hr = CoCreateInstance(clsid, nullptr, CLSCTX_LOCAL_SERVER, IID_IDispatch, (void**)&pApp);
    if (FAILED(hr) || !pApp) {
        return nullptr;
    }

    // Build temp PDF path
    WCHAR tempDirW[MAX_PATH];
    GetTempPathW(MAX_PATH, tempDirW);
    TempStr tempDir = ToUtf8Temp(tempDirW);
    TempStr basename = path::GetBaseNameTemp(pptxPath);
    TempStr noExt = path::GetPathNoExtTemp(basename);
    AutoFreeStr outPdf(str::Format("%s\\sumatrapptxpp_%s.pdf", tempDir, noExt));

    if (file::Exists(outPdf)) {
        pApp->Release();
        return outPdf.Release();
    }

    // Helper: call a method by name on an IDispatch object
    auto CallMethod = [](IDispatch* pDisp, const wchar_t* methodName, DISPPARAMS* dp, VARIANT* ret) -> HRESULT {
        DISPID dispId = 0;
        LPOLESTR names[1] = {(LPOLESTR)methodName};
        HRESULT hr2 = pDisp->GetIDsOfNames(IID_NULL, names, 1, LOCALE_USER_DEFAULT, &dispId);
        if (FAILED(hr2)) {
            return hr2;
        }
        return pDisp->Invoke(dispId, IID_NULL, LOCALE_USER_DEFAULT, DISPATCH_METHOD, dp, ret, nullptr, nullptr);
    };

    auto SetProp = [](IDispatch* pDisp, const wchar_t* propName, VARIANT* val) -> HRESULT {
        DISPID dispId = 0;
        LPOLESTR names[1] = {(LPOLESTR)propName};
        HRESULT hr2 = pDisp->GetIDsOfNames(IID_NULL, names, 1, LOCALE_USER_DEFAULT, &dispId);
        if (FAILED(hr2)) {
            return hr2;
        }
        DISPID namedArg = DISPID_PROPERTYPUT;
        DISPPARAMS dp = {val, &namedArg, 1, 1};
        return pDisp->Invoke(dispId, IID_NULL, LOCALE_USER_DEFAULT, DISPATCH_PROPERTYPUT, &dp, nullptr, nullptr,
                             nullptr);
    };

    // Set Visible = false
    VARIANT vFalse;
    VariantInit(&vFalse);
    vFalse.vt = VT_BOOL;
    vFalse.boolVal = VARIANT_FALSE;
    SetProp(pApp, L"Visible", &vFalse);

    // Get Presentations collection
    VARIANT vRet;
    VariantInit(&vRet);
    DISPPARAMS dpEmpty = {nullptr, nullptr, 0, 0};
    DISPID dispId = 0;
    LPOLESTR namesPres[1] = {(LPOLESTR)L"Presentations"};
    hr = pApp->GetIDsOfNames(IID_NULL, namesPres, 1, LOCALE_USER_DEFAULT, &dispId);
    if (FAILED(hr)) {
        pApp->Release();
        return nullptr;
    }
    hr = pApp->Invoke(dispId, IID_NULL, LOCALE_USER_DEFAULT, DISPATCH_PROPERTYGET, &dpEmpty, &vRet, nullptr, nullptr);
    if (FAILED(hr) || vRet.vt != VT_DISPATCH) {
        pApp->Release();
        return nullptr;
    }
    IDispatch* pPres = vRet.pdispVal;

    // Call Presentations.Open(path, ReadOnly=True, Untitled=True, WithWindow=False)
    TempWStr pathW = ToWStrTemp(pptxPath);
    VARIANT vArgs[4];
    VariantInit(&vArgs[0]);
    vArgs[0].vt = VT_BSTR;
    vArgs[0].bstrVal = SysAllocString(pathW); // Filename
    VariantInit(&vArgs[1]);
    vArgs[1].vt = VT_BOOL;
    vArgs[1].boolVal = VARIANT_TRUE; // ReadOnly
    VariantInit(&vArgs[2]);
    vArgs[2].vt = VT_BOOL;
    vArgs[2].boolVal = VARIANT_TRUE; // Untitled
    VariantInit(&vArgs[3]);
    vArgs[3].vt = VT_BOOL;
    vArgs[3].boolVal = VARIANT_FALSE; // WithWindow

    DISPPARAMS dpOpen = {vArgs, nullptr, 4, 0};
    VARIANT vPresObj;
    VariantInit(&vPresObj);
    hr = CallMethod(pPres, L"Open", &dpOpen, &vPresObj);
    SysFreeString(vArgs[0].bstrVal);
    pPres->Release();

    if (FAILED(hr) || vPresObj.vt != VT_DISPATCH) {
        pApp->Release();
        return nullptr;
    }
    IDispatch* pPresentation = vPresObj.pdispVal;

    // Call presentation.ExportAsFixedFormat(path, ppFixedFormatTypePDF=2)
    TempWStr outPdfW = ToWStrTemp(outPdf.Get());
    VARIANT vExArgs[2];
    VariantInit(&vExArgs[0]);
    vExArgs[0].vt = VT_BSTR;
    vExArgs[0].bstrVal = SysAllocString(outPdfW); // Path
    VariantInit(&vExArgs[1]);
    vExArgs[1].vt = VT_INT;
    vExArgs[1].intVal = 2; // ppFixedFormatTypePDF

    DISPPARAMS dpExport = {vExArgs, nullptr, 2, 0};
    VARIANT vIgnored;
    VariantInit(&vIgnored);
    hr = CallMethod(pPresentation, L"ExportAsFixedFormat", &dpExport, &vIgnored);
    SysFreeString(vExArgs[0].bstrVal);

    // Close the presentation (Close method, no args)
    DISPPARAMS dpClose = {nullptr, nullptr, 0, 0};
    VARIANT vIgnored2;
    VariantInit(&vIgnored2);
    CallMethod(pPresentation, L"Close", &dpClose, &vIgnored2);
    pPresentation->Release();

    // Quit PowerPoint
    CallMethod(pApp, L"Quit", &dpEmpty, &vIgnored);
    pApp->Release();

    if (FAILED(hr) || !file::Exists(outPdf)) {
        return nullptr;
    }
    return outPdf.Release();
}

// Try all available converters. Returns heap-allocated PDF path, or nullptr.
static char* TryConvertPptxToPdf(const char* pptxPath) {
    // 1) Try PowerPoint COM (best quality, requires MS Office)
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    char* ppPdf = ConvertPptxViaPowerPoint(pptxPath);
    CoUninitialize();
    if (ppPdf) {
        return ppPdf;
    }

    // 2) Try LibreOffice (free, requires LibreOffice installed)
    const char* sofficePath = FindLibreOfficePath();
    if (sofficePath) {
        AutoFreeStr cachePdf(BuildPptxCachePdfPath(pptxPath));
        if (file::Exists(cachePdf)) {
            return cachePdf.Release();
        }
        if (ConvertPptxViaLibreOffice(sofficePath, pptxPath, cachePdf)) {
            return cachePdf.Release();
        }
    }

    return nullptr;
}

// ===== Factory =====

EngineBase* CreateEnginePptxFromFile(const char* path) {
    // Try transparent PDF conversion for perfect fidelity rendering
    AutoFreeStr pdfPath(TryConvertPptxToPdf(path));
    if (pdfPath) {
        EngineBase* pdfEngine = CreateEngineMupdfFromFile(pdfPath, kindFilePDF, DpiGet(nullptr));
        if (pdfEngine) {
            // Override file path so UI shows the original .pptx filename
            pdfEngine->SetFilePath(path);
            return pdfEngine;
        }
    }

    // Fall back to native renderer
    auto* engine = new EnginePptx();
    if (!engine->LoadFromFile(path)) {
        delete engine;
        return nullptr;
    }
    return engine;
}
