import { readdirSync, rmSync, unlinkSync, existsSync } from "node:fs";
import { join } from "node:path";

let nSkipped = 0;
let nDirsDeleted = 0;
let nFilesDeleted = 0;

export function clearDirPreserveSettings(dir: string): void {
  let entries;
  try {
    entries = readdirSync(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const name = entry.name;
    const fullPath = join(dir, name);
    const excluded = name === "sumatrapdfcache" || name === "SumatraPDF-settings.txt" || name.includes("asan");
    if (excluded) {
      nSkipped++;
      continue;
    }
    if (entry.isDirectory()) {
      rmSync(fullPath, { recursive: true, force: true });
      nDirsDeleted++;
    } else {
      unlinkSync(fullPath);
      nFilesDeleted++;
    }
  }
}

function cleanPreserveSettings(): void {
  let entries;
  try {
    entries = readdirSync("out", { withFileTypes: true });
  } catch {
    // assuming 'out' doesn't exist, which is fine
    return;
  }
  for (const entry of entries) {
    const fullPath = join("out", entry.name);
    if (!entry.isDirectory()) {
      unlinkSync(fullPath);
      continue;
    }
    clearDirPreserveSettings(fullPath);
  }
  console.log(`clean: skipped ${nSkipped} files, deleted ${nDirsDeleted} dirs and ${nFilesDeleted} files`);
}

if (import.meta.main) {
  cleanPreserveSettings();
}
