import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {createRequire} from 'node:module';
import {root} from '../scripts/core.mjs';
const require=createRequire(import.meta.url);
let pw;try{pw=require('playwright');}catch{pw=require(path.join(os.homedir(),'.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright'));}
const args=typeof process==='undefined'?[]:process.argv;
const arg=name=>{const i=args.indexOf(name);return i>=0?args[i+1]:undefined;};
const assert=(condition,message)=>{if(!condition)throw Error(message);};
const mime={'.html':'text/html; charset=utf-8','.js':'application/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.svg':'image/svg+xml','.woff2':'font/woff2','.woff':'font/woff','.ttf':'font/ttf'};
const out=path.join(root,'test-output');fs.mkdirSync(out,{recursive:true});
export async function runBrowserChecks(existing={},options={}){
const report=[];
const directory=path.resolve(root,options.directory||arg('--directory')||'dist');
for(const name of ['chromium','webkit']){
 const browser=existing[name]||await pw[name].launch({headless:true,timeout:15000,...(arg('--'+name)?{executablePath:arg('--'+name)}:{})});
 try{
 const context=await browser.newContext({viewport:{width:1440,height:980}});
 const page=await context.newPage();page.setDefaultTimeout(10000);page.setDefaultNavigationTimeout(15000);const errors=[];page.on('pageerror',e=>errors.push(String(e)));
 // Test genuine relative URL resolution under a project sub-path without a
 // listening socket. All requests are fulfilled from the built output.
 await context.route('https://visual-paper.test/**',async route=>{
  const url=new URL(route.request().url());let file=decodeURIComponent(url.pathname.replace(/^\/HardnessBilevelProgramming\//,''));
  if(!file||file.endsWith('/'))file+='index.html';
  const full=path.resolve(directory,file);
  if(!full.startsWith(directory+path.sep)||!fs.existsSync(full)){await route.fulfill({status:404,body:'Not found'});return;}
  await route.fulfill({status:200,contentType:mime[path.extname(full)]||'application/octet-stream',body:fs.readFileSync(full)});
 });
 await page.goto('https://visual-paper.test/HardnessBilevelProgramming/');
 await page.waitForFunction(()=>window.PAPER&&document.querySelector('#result-heading'));
 // Check every generated snippet, including ones outside the selected view.
 // Rendering twice must leave the DOM unchanged and retain accessible MathML.
 const mathCheck=await page.evaluate(()=>{
  let expressions=0,snippets=0;
  function visit(value){
   if(!value||typeof value!=='object')return;
   for(const [key,item]of Object.entries(value)){
    if(typeof item==='string'&&/^(html|.*Html)$/.test(key)){
     const host=document.createElement('div');host.innerHTML=item;
     const count=host.querySelectorAll('.math').length;
     if(!count)continue;
     if(host.querySelector('.katex'))throw Error('Build still ships pre-rendered mathematics');
     PAPER_MATH.renderIn(host,PAPER.math.macros,katex);
     if(host.querySelectorAll('.katex').length!==count||host.querySelectorAll('math').length!==count)throw Error('Incomplete mathematical rendering');
     const first=host.innerHTML;PAPER_MATH.renderIn(host,PAPER.math.macros,katex);
     if(host.innerHTML!==first)throw Error('Repeated rendering changes mathematics');
     snippets++;expressions+=count;
    }else visit(item);
   }
  }
  visit(PAPER);return {snippets,expressions};
 });
 assert(mathCheck.expressions>1000,'Formula coverage is unexpectedly low');
 async function checkRendered(selector,requireMath=false){
  const host=page.locator(selector);
  assert(await host.locator('.math:not([data-math-rendered])').count()===0,name+' unrendered mathematics in '+selector);
  assert(await host.locator('.katex-error').count()===0,name+' math error in '+selector);
  if(requireMath)assert(await host.locator('.katex').count()>0,name+' missing mathematics in '+selector);
 }
 const ids=await page.evaluate(()=>PAPER.nodes.map(n=>n.id));
 for(const id of ids){
  console.log(name,id);
  await page.evaluate(id=>{location.hash='#/'+id+'/summary'},id);
  await page.waitForFunction(id=>document.querySelector('#result .result-type')?.textContent===`${PAPER.nodes.find(n=>n.id===id).kind[0].toUpperCase()+PAPER.nodes.find(n=>n.id===id).kind.slice(1)} ${PAPER.nodes.find(n=>n.id===id).number}`,id);
  await checkRendered('#result',await page.evaluate(id=>PAPER.nodes.find(n=>n.id===id).statementHtml.includes('class="math '),id));
  assert(await page.locator('#result-heading').isVisible(),name+' missing result '+id);
  const step=page.locator('#result .proof-steps details').first();
  if(await step.count()){
   await step.locator('summary').click();
   assert(await step.locator('.source-math').isVisible(),'Proof step failed to open: '+id);
  }
  const fullProof=page.locator('#result .source-details').filter({has:page.locator('.source-math')});
  if(await fullProof.count()){
   await fullProof.locator('summary').click();
   assert(await fullProof.locator('.source-math').isVisible(),'Full proof failed to open: '+id);
  }
  if(await page.evaluate(()=>Boolean(PAPER.meta.leanSnapshot))){
   const mapping=await page.evaluate(id=>PAPER.nodes.find(n=>n.id===id).lean,id);
   if(mapping.status!=='unresolved'){
    const sourcePage=await context.newPage();
    await sourcePage.goto(new URL(mapping.url,page.url()).href);
    assert((await sourcePage.locator('li:target').textContent()).includes(mapping.declaration.split('.').at(-1)),'Lean source link targets the wrong declaration: '+id);
    const back=sourcePage.getByRole('link',{name:'Visual paper'});
    assert(new URL(await back.getAttribute('href'),sourcePage.url()).pathname==='/HardnessBilevelProgramming/index.html','Lean source back link escapes sub-path');
    await sourcePage.close();
   }
  }
  if(['prop25','prop26'].includes(id)){
   const slider=page.locator('#result .quantitative-figure input[type=range]');assert(await slider.count()===1,'Figure slider absent or duplicated');
   const before=await page.locator('#result .figure-values').textContent();await slider.fill('-1');
   assert(before!==await page.locator('#result .figure-values').textContent(),'Slider failed to update');
   await page.getByRole('button',{name:'Enlarge illustration'}).click();assert(await page.locator('.figure-popout').isVisible(),'Popout missing');
   await page.locator('.figure-popout button').first().click();await page.locator('.figure-popout').waitFor({state:'detached'});
  }
 }
 await page.evaluate(()=>{location.hash='#/thm215/summary'});await page.waitForTimeout(80);
 const symbol=page.locator('#result [data-notation="sa"]').first();await symbol.click();assert(await page.locator('#notation-dialog').isVisible(),'Notation dialog failed');await checkRendered('#notation-content',true);await page.keyboard.press('Escape');
 await page.keyboard.press('/');assert(await page.locator('#search-dialog').isVisible(),'Search keyboard shortcut failed');await page.locator('#search-input').fill('growth');assert(await page.locator('#search-results [data-result]').count()>0,'Search has no results');await page.keyboard.press('Escape');
 await page.locator('#view-focus').click();await page.locator('#view-whole').click();
 await page.getByRole('link',{name:'Corrections',exact:true}).click();assert(await page.locator('#corrections-view').isVisible(),'Correction view missing');
 await checkRendered('#corrections-view');
 await page.getByRole('link',{name:'Proof map',exact:true}).click();
 await page.evaluate(()=>document.documentElement.dataset.theme='dark');await page.screenshot({path:path.join(out,name+'-dark.png')});
 await page.evaluate(()=>document.documentElement.dataset.theme='light');
 await page.setViewportSize({width:390,height:844});await page.evaluate(()=>{location.hash='#/prop25/summary'});await page.waitForTimeout(80);
 assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1),'Mobile horizontal overflow');
 await page.screenshot({path:path.join(out,name+'-mobile.png')});
 await page.setViewportSize({width:1440,height:980});await page.evaluate(()=>{location.hash='#/thm215/summary'});await page.waitForTimeout(80);
 await page.screenshot({path:path.join(out,name+'-desktop.png')});
 const local=await context.newPage();local.on('pageerror',e=>errors.push(String(e)));
 await local.goto('file://'+path.join(directory,'index.html')+'#/thm215/summary');
 await local.waitForFunction(()=>document.querySelector('#result .katex'));
 assert(await local.locator('#result .math:not([data-math-rendered])').count()===0,'Direct file access leaves unrendered math');
 await local.close();
 assert(errors.length===0,name+' errors: '+errors.join('; '));
 report.push({engine:name,version:browser.version(),directory:path.basename(directory),results:ids.length,math:mathCheck,errors,checks:['project-subpath','file-access','all-results','Lean-source-links','browser-math','all-math-snippets','math-idempotence','MathML','proof-steps','full-proofs','interactive-figures','figure-popouts','notation','search','focus','corrections','mobile','dark-theme']});
 await context.close();
 }finally{if(!existing[name])await browser.close();}
}
fs.writeFileSync(path.join(root,'reports/browser-checks.json'),JSON.stringify(report,null,2));
console.log(JSON.stringify(report,null,2));
return report;
}
if(args[1]?.endsWith('/test/browser.mjs'))await runBrowserChecks();
