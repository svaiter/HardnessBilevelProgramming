import fs from 'node:fs';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {root,sha,readJSON} from './core.mjs';

// A location index, not a Lean parser or kernel check. Comments are masked before
// looking for commands so commented-out declarations cannot satisfy a mapping.
export function maskComments(text, maskStrings=false) {
 let out='',depth=0,string=false;
 for(let i=0;i<text.length;i++){
  const c=text[i],next=text[i+1];
  if(depth){
   if(c==='/'&&next==='-'){depth++;out+='  ';i++;}
   else if(c==='-'&&next==='/'){depth--;out+='  ';i++;}
   else out+=c==='\n'?'\n':' ';
  }else if(string){
   out+=maskStrings?(c==='\n'?'\n':' '):c;
   if(c==='\\'&&next!==undefined){out+=maskStrings?' ':next;i++;}
   else if(c==='"')string=false;
  }else if(c==='/'&&next==='-'){depth=1;out+='  ';i++;}
  else if(c==='-'&&next==='-'){while(i<text.length&&text[i]!=='\n'){out+=' ';i++;}if(i<text.length)out+='\n';}
  else if(c==='"'){string=true;out+=maskStrings?' ':c;}
  else out+=c;
 }
 return out;
}
export function codeHash(text){
 // Retain string contents exactly; ignore comments and whitespace between tokens.
 return sha((maskComments(text).match(/"(?:\\.|[^"\\])*"|[^\s]+/g)||[]).join(' '));
}
export function indexLean(file,text){
 const code=maskComments(text,true),stack=[],entries=[];
 let offset=0;
 for(const line of code.split('\n')){
  const control=line.match(/^\s*(?:noncomputable\s+)?(namespace|section|end)\b\s*([^\s]*)/);
  if(control){
   if(control[1]==='end')stack.pop();
   else stack.push({kind:control[1],name:control[2]||''});
  }
  const m=line.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|local)\s+)*(?:theorem|lemma|def|abbrev|instance|class|structure|opaque|axiom)\s+([^\s:({\[]+)/);
  if(m){
   const name=m[1];
   if(!name.startsWith('«')&&!name.includes('»')){
    const prefix=stack.filter(s=>s.kind==='namespace').map(s=>s.name).filter(Boolean).join('.');
    const declaration=name.startsWith('_root_.')?name.slice(7):[prefix,name].filter(Boolean).join('.');
    entries.push({declaration,file,line:text.slice(0,offset).split('\n').length});
   }
  }
  offset+=line.length+1;
 }
 return entries;
}
export const isLeanInput=file=>file.endsWith('.lean')||['lakefile.toml','lake-manifest.json','lean-toolchain'].includes(file);
function git(repo,args){return execFileSync('git',['--no-optional-locks','-C',repo,...args],{encoding:'utf8',maxBuffer:40e6});}
export function readGitSnapshot(repo,ref){
 const commit=git(repo,['rev-parse','--verify',ref+'^{commit}']).trim();
 const names=git(repo,['ls-tree','-r','--name-only',commit]).trim().split('\n').filter(isLeanInput).filter(f=>!f.startsWith('visual-paper/'));
 return {commit,files:Object.fromEntries(names.map(f=>[f,git(repo,['show',commit+':'+f])])),workingTree:false,dirty:false};
}
export function readWorkingSnapshot(repo){
 const head=readGitSnapshot(repo,'HEAD');
 const names=git(repo,['ls-files','--cached','--others','--exclude-standard','-z']).split('\0').filter(isLeanInput).filter(f=>!f.startsWith('visual-paper/'));
 const files={};
 for(const f of [...new Set(names)].sort()){
  const p=path.join(repo,f);if(!fs.existsSync(p))continue;
  if(fs.lstatSync(p).isSymbolicLink())throw Error('Lean snapshot does not follow symlinks: '+f);
  files[f]=fs.readFileSync(p,'utf8');
 }
 const dirty=JSON.stringify(Object.keys(files).sort())!==JSON.stringify(Object.keys(head.files).sort())||Object.keys(files).some(f=>files[f]!==head.files[f]);
 return {...head,files,workingTree:true,dirty};
}
export function resolveMappings(files,map,baseline){
 const index=Object.entries(files).filter(([f])=>f.endsWith('.lean')).flatMap(([f,t])=>indexLean(f,t));
 const changedFiles=[...new Set([...Object.keys(files),...Object.keys(baseline.files)])].filter(f=>!(f in files)||!(f in baseline.files)||codeHash(files[f])!==baseline.files[f]).sort();
 const nodes={},issues=[];
 for(const[id,mapping]of Object.entries(map.nodes)){
  // Prefer the mapped file, then allow an unambiguous move to another file.
  const matches=index.filter(d=>d.declaration===mapping.declaration);
  const preferred=matches.filter(d=>d.file===mapping.file);
  const candidates=preferred.length?preferred:matches;
  if(candidates.length!==1){
   const reason=candidates.length?'ambiguous':'missing';
   issues.push({node:id,declaration:mapping.declaration,reason,candidates:matches});
   nodes[id]={...mapping,status:'unresolved',reason};continue;
  }
  const found=candidates[0];
  const changed=changedFiles.length>0;
  nodes[id]={...mapping,...found,status:changed?'source-changed':mapping.status,previousStatus:mapping.status,
   reason:changed?'Lean code or dependencies differ from the reviewed snapshot. Paper correspondence and Lean build need checking.':null};
 }
 return {index,nodes,changedFiles,issues};
}
export function loadLeanSnapshot(){
 if(!fs.existsSync(path.join(root,'LEAN.lock.json')))return null;
 const lock=readJSON('LEAN.lock.json');
 if(sha(fs.readFileSync(path.join(root,'content/lean-map.json')))!==lock.mapSha256)throw Error('Lean mapping changed: run npm run update.');
 if(sha(fs.readFileSync(path.join(root,'content/lean-baseline.json')))!==lock.baselineSha256)throw Error('Lean baseline changed: run npm run update.');
 for(const[file,hash]of Object.entries(lock.files)){
  const p=path.resolve(root,'source/lean',file);
  if(!p.startsWith(path.join(root,'source/lean')+path.sep)||sha(fs.readFileSync(p))!==hash)throw Error('Lean snapshot changed: '+file+'; run npm run update.');
 }
 return lock;
}
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
export function emitLeanPages(lock,out){
 const dir=path.join(out,'lean');fs.rmSync(dir,{recursive:true,force:true});
 if(!lock)return;
 for(const file of new Set(Object.values(lock.nodes).filter(n=>n.status!=='unresolved').map(n=>n.file))){
  const target='lean/'+file+'.html',dest=path.join(out,target);fs.mkdirSync(path.dirname(dest),{recursive:true});
  const source=fs.readFileSync(path.join(root,'source/lean',file),'utf8');
  const back=path.posix.relative(path.posix.dirname(target),'index.html');
  const github=lock.dirty?'':`${lock.repository}/blob/${lock.commit}/${file}`;
  fs.writeFileSync(dest,`<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${esc(file)} — Lean source</title><style>body{margin:24px;color:#23342d;background:#f7f5ee;font:15px system-ui}a{color:#245a50}header{position:sticky;top:0;background:#f7f5ee;padding:12px 0}ol{padding-left:5em}li{padding:0 12px;white-space:pre;font:13px/1.6 monospace}li{scroll-margin-top:160px}li:target{background:#f6df9c}li::marker{color:#78867e}.code{overflow:auto}h1{font-size:20px}</style><header><a href="${back}">← Visual paper</a><h1>${esc(file)}</h1><p>${lock.dirty?'Local source snapshot based on ':''}${esc(lock.commit)}${github?` · <a href="${esc(github)}">GitHub</a>`:''}</p></header><div class="code"><ol>${source.split('\n').map((line,i)=>`<li id="L${i+1}">${esc(line)||' '}</li>`).join('')}</ol></div></html>`);
 }
}
