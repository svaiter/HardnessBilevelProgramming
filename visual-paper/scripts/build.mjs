import fs from 'node:fs';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import katex from '../vendor/katex/package/dist/katex.mjs';
import '../site/math.js';
import {root,readJSON,source,extract,walk,validate,lineOf,sourceURL} from './core.mjs';
import {loadLeanSnapshot,emitLeanPages} from './lean-sources.mjs';

const data=readJSON('content/paper.json');
const report=validate(data,{release:process.argv.includes('--release')});
const leanSnapshot=loadLeanSnapshot();
if(process.argv.includes('--release')&&leanSnapshot&&(leanSnapshot.changedFiles.length||leanSnapshot.issues.length))throw Error('Lean snapshot differs from reviewed correspondence; check mappings before a reviewed release.');
const out=path.join(root,'dist-next');fs.rmSync(out,{recursive:true,force:true});fs.mkdirSync(out,{recursive:true});
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const decode=s=>s.replace(/&amp;/g,'&').replace(/&lt;/g,'<').replace(/&gt;/g,'>').replace(/&quot;/g,'"').replace(/&#39;/g,"'");
const tex=source('source/paper/main.tex');
const aux=source('source/paper/main.aux');
const labels={};
for(const m of aux.matchAll(/\\newlabel\{([^}]+)\}\{\{/g))if(!m[1].endsWith('@cref'))labels[m[1]]=brace(aux,m.index+m[0].length-1)[0];
const citations={};for(const m of aux.matchAll(/\\bibcite\{([^}]+)\}\{([^}]+)\}/g))citations[m[1]]=m[2];
function brace(s,i){let depth=1,start=i+1;for(i++;i<s.length;i++){if(s[i]==='\\'){i++;continue;}if(s[i]==='{')depth++;if(s[i]==='}'&&!--depth)return[s.slice(start,i),i+1];}throw Error('Unbalanced macro');}
const macros={};
const preamble=tex.slice(0,tex.indexOf('\\begin{document}'));
const command=/\\(?:newcommand|renewcommand)\*?\s*\{(\\[A-Za-z]+)\}\s*(?:\[(\d+)\])?\s*\{/g;
for(let m;(m=command.exec(preamble));){const[value,end]=brace(preamble,command.lastIndex-1);macros[m[1]]=value;command.lastIndex=end;}
Object.assign(macros,{'\\mathds':'\\mathbb','\\llbracket':'[\\![','\\rrbracket':']\\!]'});
fs.writeFileSync(path.join(root,'site/macros.json'),JSON.stringify(macros,null,2));
const notationMacros={'\\SA':'sa','\\LSC':'lsc','\\USC':'usc','\\BC':'cb','\\PP':'pp','\\cY':'yset','\\valoptim':'optimistic','\\valpessim':'pessimistic','\\valbilevel':'optimistic','\\existleveltwo':'sigma2'};
const renderMacros={...macros};
for(const[macro,id]of Object.entries(notationMacros))renderMacros[macro]=`\\htmlClass{notation-ref notation--${id}}{${macros[macro]}}`;
let mathCount=0;const rendered=new Map();
function cleanTeX(t){
 t=t.replace(/\\iffalse\b[\s\S]*?\\fi\b/g,'').replace(/(?<!\\)%[^\n]*/g,'');
 t=t.replace(/\\label\{[^}]*\}/g,'');
 t=t.replace(/\\(?:eqref|Cref|cref|ref)\{([^}]+)\}/g,(_m,id)=>labels[id]||id);
 t=t.replace(/\\cite(?:\[([^\]]*)\])?\{([^}]+)\}/g,(_m,note,ids)=>'['+ids.split(',').map(id=>citations[id.trim()]||id).join(', ')+(note?', '+note:'')+']');
 t=t.replace(/\\(?:begin|end)\{(?:theorem|proposition|lemma|corollary|definition|problem|remark|proof)\*?\}(?:\[[^\]]*\])?/g,'');
 return t;
}
function balanceFragment(t){
 const stack=[];const prefix=[];
 if(/^\s*\\item\b/.test(t))t='\\begin{enumerate}\n'+t;
 for(const m of t.matchAll(/\\(begin|end)\{([^}]+)\}/g)){
  if(m[1]==='begin')stack.push(m[2]);
  else if(stack.at(-1)===m[2])stack.pop();
  else prefix.unshift(m[2]);
 }
 // A proof cut may start or end inside an itemized list; add only structural
 // wrappers for rendering. Stored source text and audited offsets stay exact.
 return (prefix.map(e=>'\\begin{'+e+'}').join('\n')+t+stack.reverse().map(e=>'\\end{'+e+'}').join('\n')).replace(/\\begin\{([^}]+)\}\s*\\end\{\1\}/g,'');
}
function render(t,format='markdown',fragment=false){
 if(!t)return'';const key=format+'\n'+fragment+'\n'+t;if(rendered.has(key))return rendered.get(key);
 const cleaned=format==='latex'?cleanTeX(t):t;
 const input=fragment?balanceFragment(cleaned):cleaned;
 const p=spawnSync('pandoc',['--from',format==='latex'?'latex':'markdown+tex_math_dollars+tex_math_single_backslash','--to','html5','--mathjax','--wrap=none'],{input,encoding:'utf8',maxBuffer:15e6});
 if(p.status!==0){fs.writeFileSync(path.join(root,'reports/render-failure.txt'),input);throw Error('Pandoc: '+p.stderr+' (see reports/render-failure.txt)');}
 let html=p.stdout.replace(/<span class="math (inline|display)">([\s\S]*?)<\/span>/g,(span,type,raw)=>{
  // Validate using the exact browser renderer, but ship only the original TeX.
  globalThis.PAPER_MATH.renderToString(decode(raw),type==='display',renderMacros,katex);
  mathCount++;
  return span;
 });
 // Preserve source quotation markup, without allowing scriptable source HTML.
 html=html.replace(/<script\b[\s\S]*?<\/script>/gi,'');
 rendered.set(key,html);return html;
}
walk(data,v=>{if(typeof v.text==='string'&&Array.isArray(v.cites)){v.html=render(v.text);v.cites=v.cites.map(a=>({...a,url:sourceURL(a),line:lineOf(a)}));}});
for(const node of data.nodes){
 node.main=['thm11','thm212','thm215','thm221','thm32'].includes(node.id);
 node.statementText=extract(node.statement);node.statementHtml=render(node.statementText,node.statement.file.endsWith('.tex')?'latex':'markdown');
 node.source={url:sourceURL(node.statement),label:node.sourceKind==='blueprint'?'Repository blueprint':'arXiv v2 · exact source',line:lineOf(node.statement)};
 if(node.proof){
  node.proofText=extract(node.proof);node.proofHtml=render(node.proofText,node.proof.file.endsWith('.tex')?'latex':'markdown');
  for(const step of node.steps){step.text=Array.from(source(node.proof.file)).slice(step.start,step.end).join('');step.html=render(step.text,node.proof.file.endsWith('.tex')?'latex':'markdown',node.proof.file.endsWith('.tex'));}
 }
 if(leanSnapshot){
  const mapping=leanSnapshot.nodes[node.id];
  if(node.lean&&!mapping)throw Error('Missing Lean mapping for '+node.id+'; edit content/lean-map.json and run npm run update.');
  if(mapping)node.lean={...mapping,url:mapping.status==='unresolved'?'':`lean/${mapping.file}.html#L${mapping.line}`};
 }else if(node.lean?.file)node.lean.url=`https://github.com/svaiter/HardnessBilevelProgramming/blob/${readJSON('SOURCE.lock').lean.commit}/${node.lean.file}${node.lean.line?'#L'+node.lean.line:''}`;
}
for(const item of data.notation||[])item.html=render(item.symbol.includes('$')?item.symbol:'$'+item.symbol+'$');
data.math={macros:renderMacros};
data.meta={title:'Geometric and computational hardness of bilevel programming',authors:'J. Bolte · T. Lê · E. Pauwels · S. Vaiter',arxiv:'https://arxiv.org/abs/2407.12372v2',repository:'https://github.com/svaiter/HardnessBilevelProgramming',commit:readJSON('SOURCE.lock').lean.commit,year:2025,preview:!process.argv.includes('--release'),audit:{claims:report.claims,reviewed:report.audited},citation:'J. Bolte, T. Lê, E. Pauwels, S. Vaiter. Geometric and computational hardness of bilevel programming. Mathematical Programming (2025). arXiv:2407.12372.'};
if(leanSnapshot){data.meta.commit=leanSnapshot.commit;data.meta.leanSnapshot={dirty:leanSnapshot.dirty,changedFiles:leanSnapshot.changedFiles.length,issues:leanSnapshot.issues.length,buildChecked:false};}
for(const filename of fs.readdirSync(path.join(root,'site'))){if(filename.endsWith('.json'))continue;fs.copyFileSync(path.join(root,'site',filename),path.join(out,filename));}
fs.mkdirSync(path.join(out,'vendor'),{recursive:true});
for(const[from,to]of [
 ['katex/package/dist/katex.min.css','katex.min.css'],['katex/package/dist/katex.min.js','katex.min.js'],['cytoscape/package/dist/cytoscape.min.js','cytoscape.min.js'],['dagre/package/dist/dagre.min.js','dagre.min.js'],['cytoscape-dagre/package/cytoscape-dagre.js','cytoscape-dagre.js']
])fs.copyFileSync(path.join(root,'vendor',from),path.join(out,'vendor',to));
fs.cpSync(path.join(root,'vendor/katex/package/dist/fonts'),path.join(out,'vendor/fonts'),{recursive:true});
fs.writeFileSync(path.join(out,'data.js'),'window.PAPER='+JSON.stringify(data).replace(/</g,'\\u003c')+';\n');
fs.writeFileSync(path.join(out,'.nojekyll'),'');
emitLeanPages(leanSnapshot,out);
const licences=['Third-party dependencies bundled for offline rendering.\nPaper text remains subject to its original rights; no new licence is granted.\n'];
for(const name of ['katex','cytoscape','dagre','cytoscape-dagre']){const p=path.join(root,'vendor',name,'package');const file=fs.readdirSync(p).find(f=>/^licen[sc]e/i.test(f));if(file)licences.push(name+'\n'+fs.readFileSync(path.join(p,file),'utf8'));}
fs.writeFileSync(path.join(out,'THIRD_PARTY_LICENSES.txt'),licences.join('\n\n'));
fs.rmSync(path.join(root,'dist'),{recursive:true,force:true});fs.renameSync(out,path.join(root,'dist'));
const fullReport={...report,mathExpressions:mathCount,renderedSnippets:rendered.size,mathRendering:'browser KaTeX; validated during build',dataBytes:fs.statSync(path.join(root,'dist/data.js')).size,mode:data.meta.preview?'author-review preview':'release'};
fs.writeFileSync(path.join(root,'reports/build.json'),JSON.stringify(fullReport,null,2));
console.log(JSON.stringify({...fullReport,pending:fullReport.pending.length},null,2));
