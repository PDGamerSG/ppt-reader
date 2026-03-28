import { $ } from "bun";
import { join } from "node:path";

const dir = join("tools", "logview-web");
console.log(`running logview-web in ${dir}`);
await $`go run . -run-dev`.cwd(dir);
