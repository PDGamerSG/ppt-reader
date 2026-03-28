import { $ } from "bun";
import { existsSync, statSync, readFileSync, rmSync } from "node:fs";
import { join } from "node:path";

const logViewWinDir = join("tools", "logview");

function extractLogViewVersion(): string {
  const path = join(logViewWinDir, "frontend", "src", "version.js");
  const content = readFileSync(path, "utf-8");
  // looks like: export const version = "0.1.2";
  const firstLine = content.split("\n")[0];
  const parts = firstLine.split(" ");
  if (parts.length !== 5) {
    throw new Error(`unexpected version.js format: ${firstLine}`);
  }
  const ver = parts[4].replace(/[";]/g, "");
  const verParts = ver.split(".");
  if (verParts.length < 2) {
    throw new Error(`version must be at least x.y: ${ver}`);
  }
  for (const part of verParts) {
    const n = parseInt(part, 10);
    if (isNaN(n) || n > 100) {
      throw new Error(`invalid version part: ${part}`);
    }
  }
  return ver;
}

function formatSize(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
  return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
}

async function main() {
  const ver = extractLogViewVersion();
  console.log(`buildLogView: ver: ${ver}`);

  const binDir = join(logViewWinDir, "build", "bin");
  rmSync(binDir, { recursive: true, force: true });

  await $`wails build -clean -f -upx`.cwd(logViewWinDir);

  const exePath = join(binDir, "logview.exe");
  if (!existsSync(exePath)) {
    console.error(`expected ${exePath} to exist after build`);
    process.exit(1);
  }
  const size = statSync(exePath).size;
  console.log(`\n${exePath}: ${formatSize(size)}`);
}

await main();
