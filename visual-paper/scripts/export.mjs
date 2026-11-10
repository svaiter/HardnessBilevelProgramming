import fs from 'node:fs';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {root,readJSON} from './core.mjs';

const args=process.argv.slice(2);
if(args.some(arg=>arg!=='--svssg') || args.length>1)throw Error('Usage: npm run export -- [--svssg]');
execFileSync(process.execPath,[path.join(root,'scripts/build.mjs')],{stdio:'inherit'});
const integrated=args.includes('--svssg');
const dist=path.join(root,'dist'),output=path.join(root,integrated?'website-svssg':'website'),stage=path.join(root,integrated?'website-svssg-next':'website-next');
if(fs.existsSync(stage))throw Error('website-next already exists; inspect it before retrying.');
fs.cpSync(dist,stage,{recursive:true});
if(integrated){
 const html=fs.readFileSync(path.join(stage,'index.html'),'utf8');
 const body=html.slice(html.indexOf('  <main id="main">'),html.lastIndexOf('</body>'))
  .replace('<main id="main">','<div id="main">').replace('</main>','</div>')
  .replace(/\s*<footer class="site-footer">[\s\S]*?<\/footer>/,'');
 const css=fs.readFileSync(path.join(stage,'styles.css'),'utf8')
  .replace(/@font-face\s*\{[^}]*\}\s*/g,'')
  .replace(/:root/g,':scope')
  .replace(/\bmain(?=\s*\{)/g,'#main');
 fs.writeFileSync(path.join(stage,'styles.css'),'@scope (.visual-paper) {\n'+css+'\n}\n'+
  '.content .visual-paper #main { max-width: none; margin: 0; padding: 0; }\n'+
  '.content .visual-paper .hero h1 { display: none; }\n'+
  '.content .visual-paper .hero { padding: 1rem 0; }\n'+
  '.content .visual-paper .reader-content { padding: 1rem 0; }\n'+
  '.content .visual-paper h3.reading-label { font: 600 10px/1.4 var(--sans); letter-spacing: .13em; text-transform: uppercase; margin: 0 0 8px; padding: 0; border: 0; }\n'+
  '.content .visual-paper .statement-box h3.reading-label { margin-bottom: 6px; }\n'+
  '.content .visual-paper .result-correction-entry > h4 { margin: 0 0 3px; }\n'+
  '.content .visual-paper .statement-box p:last-child, .content .visual-paper .result-correction p:last-child { margin-bottom: 0; }\n');
 const assets=['styles.css'].map(f=>`#+html_head: <link rel="stylesheet" href="${f}">`)
  .concat(['vendor/cytoscape.min.js','vendor/dagre.min.js','vendor/cytoscape-dagre.js','data.js','/assets/js/mathjax-config.js','mathjax-integration.js','/assets/js/mathjax/tex-svg-full.js','figures.js','app.js'].map(f=>`#+html_head: <script defer src="${f}"></script>`)).join('\n');
 const org=`#+title: Geometric and computational hardness of bilevel programming\n#+description: An interactive reading companion and proof map.\n#+date: 2025-01-28\n#+status: finished\n#+layout: monopage\n#+options: toc:nil\n${assets}\n\n#+begin_export html\n<div class="visual-paper">\n${body}\n</div>\n#+end_export\n`;
 fs.writeFileSync(path.join(stage,'bolte2025geometric.org'),org);
 fs.rmSync(path.join(stage,'index.html'));
 for(const f of ['vendor/katex.min.css','vendor/katex.min.js','vendor/fonts','math.js'])fs.rmSync(path.join(stage,f),{recursive:true,force:true});
 for(const f of fs.readdirSync(stage))if(f.endsWith('.woff2')||f==='favicon.svg')fs.rmSync(path.join(stage,f));
}
fs.writeFileSync(path.join(stage,'BUILD_INFO.json'),JSON.stringify({paper:readJSON('SOURCE.lock').paper.arxiv,
 lean:fs.existsSync(path.join(root,'LEAN.lock.json'))?{commit:readJSON('LEAN.lock.json').commit,localChanges:readJSON('LEAN.lock.json').dirty}:readJSON('SOURCE.lock').lean,
 note:'Static visual paper. Source and maintenance instructions live in the visual-paper project, not in this upload directory.'},null,2)+'\n');
fs.rmSync(output,{recursive:true,force:true});fs.renameSync(stage,output);
// The archive expands to one directory, ready to copy to any static web host.
execFileSync('python3',['-c',
 'from pathlib import Path; import sys,zipfile; p=Path(sys.argv[1]); z=zipfile.ZipFile(sys.argv[2],"w",zipfile.ZIP_DEFLATED); [z.write(f,Path("bilevel-hardness")/f.relative_to(p)) for f in sorted(p.rglob("*")) if f.is_file()]; z.close()',
 output,path.join(root,integrated?'bilevel-hardness-svssg.zip':'bilevel-hardness-website.zip')],{stdio:'inherit'});
console.log('Export directory: '+output+'\nArchive: '+path.join(root,integrated?'bilevel-hardness-svssg.zip':'bilevel-hardness-website.zip'));
