#!/usr/bin/env node
// Run pages-dev first. Uses the same ignored Playwright install as capture_readme_figures.mjs.
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const sourceFiles = ["pages/proof-map.js", "pages/proof-map.css", "pages/figures/strata.css", "pages/style.css", "scripts/pages_proof_map.py", "scripts/capture_proof_map.mjs"];
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const sources = Object.fromEntries(sourceFiles.map((name) => [name, hash(readFileSync(join(root,name)))]));
const images = ["docs/images/proof-map-treemap.png", "thesis/assets/proof-map-treemap.png"];
const metadata = join(root,"docs/images/proof-map-treemap.json");

if (process.argv.includes("--check")) {
  const record = JSON.parse(readFileSync(metadata));
  if (JSON.stringify(record.sources) !== JSON.stringify(sources) || images.some((name)=>hash(readFileSync(join(root,name))) !== record.image)) {
    throw new Error("Proof-map screenshot drifted. Run node scripts/capture_proof_map.mjs with pages-dev running.");
  }
  console.log("Proof-map screenshot: sources and both image copies match.");
} else {
  const { chromium } = createRequire(join(root,"build/capture/package.json"))("playwright-core");
  const browser = await chromium.launch(process.env.CHROME_PATH ? {executablePath:process.env.CHROME_PATH} : {channel:"chrome"});
  try {
    const page = await browser.newPage({viewport:{width:1800,height:1200}, deviceScaleFactor:2, reducedMotion:"reduce"});
    const errors=[]; page.on("pageerror",(error)=>errors.push(error.message));
    const base = process.env.PROOF_MAP_BASE || "http://localhost:8000";
    await page.goto(`${base}/proof-map.html?view=treemap`);
    await page.locator("#wheel[data-layout=treemap][data-animating=false]").waitFor();
    await page.waitForFunction(()=>document.querySelector("#map-status").hidden);
    await page.evaluate(()=>document.fonts.ready);
    await page.mouse.move(0,0);
    // Crop to actual painted pixels, so changes in viewport padding cannot enter the figure.
    const clip = await page.locator("#wheel").evaluate((canvas)=>{
      const {width,height}=canvas, pixels=canvas.getContext("2d").getImageData(0,0,width,height).data;
      let x0=width,y0=height,x1=0,y1=0;
      for(let y=0;y<height;y++)for(let x=0;x<width;x++)if(pixels[(y*width+x)*4+3]){x0=Math.min(x0,x);x1=Math.max(x1,x);y0=Math.min(y0,y);y1=Math.max(y1,y);}
      const rect=canvas.getBoundingClientRect(), ratio=rect.width/width;
      return {x:rect.x+x0*ratio-3,y:rect.y+y0*ratio-3,width:(x1-x0+1)*ratio+6,height:(y1-y0+1)*ratio+6};
    });
    if(errors.length)throw new Error(errors.join("\n"));
    const image=await page.screenshot({clip});
    for(const name of images){mkdirSync(dirname(join(root,name)),{recursive:true});writeFileSync(join(root,name),image);}
    const data=await page.evaluate(async()=>await (await fetch("assets/proof-map.json")).json());
    writeFileSync(metadata,JSON.stringify({sources,image:hash(image),exported:data.exported,data:data.sha256},null,2)+"\n");
    console.log(`Captured treemap: ${Math.round(clip.width*2)} × ${Math.round(clip.height*2)} pixels; export ${data.exported}.`);
  } finally {await browser.close();}
}
