import fs from 'node:fs';
import path from 'node:path';
import {root,sha,readJSON} from './core.mjs';
import {readGitSnapshot,readWorkingSnapshot,resolveMappings,codeHash} from './lean-sources.mjs';

const args=process.argv.slice(2);
if(args.includes('--help')){
 console.log('npm run update [-- --ref HEAD] [-- --repo /path/to/repository]\nDefault: current working tree, including uncommitted Lean edits. No fetch, commit, push, or Lean build.');process.exit(0);
}
function option(name){const i=args.indexOf(name);if(i<0)return null;if(!args[i+1]||args[i+1].startsWith('--'))throw Error('Missing value for '+name);return args[i+1];}
for(let i=0;i<args.length;i++){if(!['--repo','--ref'].includes(args[i]))throw Error('Unknown argument '+args[i]);i++;}
const repo=path.resolve(option('--repo')||path.join(root,'..'));
const ref=option('--ref');
const snapshot=ref?readGitSnapshot(repo,ref):readWorkingSnapshot(repo);
const map=readJSON('content/lean-map.json'),baseline=readJSON('content/lean-baseline.json');
const resolved=resolveMappings(snapshot.files,map,baseline);
const folder=path.join(root,'source/lean'),temporary=path.join(root,'source/lean-next');
if(fs.existsSync(temporary))throw Error('Previous refresh left source/lean-next; inspect and remove it before retrying.');
fs.mkdirSync(temporary,{recursive:true});
try{
 for(const[file,text]of Object.entries(snapshot.files)){
  const target=path.resolve(temporary,file);if(!target.startsWith(temporary+path.sep))throw Error('Unsafe source path '+file);
  fs.mkdirSync(path.dirname(target),{recursive:true});fs.writeFileSync(target,text);
 }
const lock={schema:1,repository:map.repository,commit:snapshot.commit,dirty:snapshot.dirty,mode:ref?'commit':'working-tree',
  baselineCommit:baseline.commit,mapSha256:sha(fs.readFileSync(path.join(root,'content/lean-map.json'))),
  baselineSha256:sha(fs.readFileSync(path.join(root,'content/lean-baseline.json'))),
  files:Object.fromEntries(Object.entries(snapshot.files).map(([f,t])=>[f,sha(t)])),
  nodes:resolved.nodes,changedFiles:resolved.changedFiles,issues:resolved.issues,buildChecked:false};
 fs.rmSync(folder,{recursive:true,force:true});fs.renameSync(temporary,folder);
 fs.writeFileSync(path.join(root,'LEAN.lock.json'),JSON.stringify(lock,null,2)+'\n');
 const report={commit:lock.commit,dirty:lock.dirty,mappedNodes:Object.keys(lock.nodes).length,
  changedFiles:lock.changedFiles,unresolved:lock.issues,declarations:resolved.index.length,
  note:'Source correspondence only; no Lean build or paper re-audit performed.'};
 fs.mkdirSync(path.join(root,'reports'),{recursive:true});
 fs.writeFileSync(path.join(root,'reports/lean-update.json'),JSON.stringify(report,null,2)+'\n');
 fs.writeFileSync(path.join(root,'reports/lean-index.json'),JSON.stringify(resolved.index,null,2)+'\n');
 console.log(JSON.stringify(report,null,2));
 if(resolved.issues.length){console.error('Missing or ambiguous mappings: edit content/lean-map.json and rerun. The site will display unresolved badges.');}
}catch(error){fs.rmSync(temporary,{recursive:true,force:true});throw error;}
