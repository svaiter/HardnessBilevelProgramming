/* Quantitative illustrations of the two examples recorded in blueprint E-1/E-8.
   Mathematical captions and formulae are supplied by the cited content layer. */
(()=>{
 const NS='http://www.w3.org/2000/svg';
 function el(name,attrs={},text=''){const n=document.createElementNS(NS,name);for(const[k,v]of Object.entries(attrs))n.setAttribute(k,v);if(text)n.textContent=text;return n;}
 function html(name,attrs={},text=''){const n=document.createElement(name);for(const[k,v]of Object.entries(attrs))n.setAttribute(k,v);if(text)n.textContent=text;return n;}
 function draw(host,figure,kind,popout=false){
  const box=html('div',{class:'quantitative-figure'});host.append(box);
  const svg=el('svg',{viewBox:'0 0 520 258',role:'img','aria-label':kind==='growth'?'Numerical plot of reciprocal epsilon':'Numerical plot of the positive hyperbola branch'});box.append(svg);
  const x0=52,y0=216,w=430,h=185;
  svg.append(el('path',{d:`M ${x0} 20 V ${y0} H 498`,fill:'none',stroke:'var(--muted, #777)','stroke-width':'1'}));
  const slider=html('input',{type:'range',min:kind==='growth'?'-1.7':'-1',max:kind==='growth'?'0':'0.176',step:'0.01',value:kind==='growth'?'-0.7':'-0.3','aria-label':kind==='growth'?'Epsilon':'Parameter t'});
  const label=html('label',{class:'figure-slider-label'},kind==='growth'?'ε':'t');label.append(slider);
  const values=html('output',{class:'figure-values','aria-live':'polite'});
  const controls=html('div',{class:'figure-controls'});controls.append(label,values);box.append(controls);
  const xMax=kind==='growth'?1:1.6,yMax=kind==='growth'?50:10;
  const X=x=>x0+w*x/xMax,Y=y=>y0-h*y/yMax;
  for(const x of kind==='growth'?[0,.25,.5,.75,1]:[0,.4,.8,1.2,1.6]){
   svg.append(el('path',{d:`M${X(x)} ${y0}v5`,stroke:'var(--muted, #777)'}),el('text',{x:X(x),y:238,'text-anchor':'middle',fill:'var(--muted, #777)','font-size':'11'},String(x)));
  }
  for(const y of kind==='growth'?[0,10,20,30,40,50]:[0,2,4,6,8,10]){
   svg.append(el('path',{d:`M${x0} ${Y(y)}H498`,stroke:'var(--line, #ddd)','stroke-width':'.6'}),el('text',{x:42,y:Y(y)+4,'text-anchor':'end',fill:'var(--muted, #777)','font-size':'11'},String(y)));
  }
  const samples=Array.from({length:220},(_,i)=>{const x=(kind==='growth'?.02:.1)+(xMax-(kind==='growth'?.02:.1))*i/219;return[X(x),Y(1/x)]});
  svg.append(el('path',{d:samples.map((p,i)=>(i?'L':'M')+p.join(' ')).join(' '),fill:'none',stroke:'var(--teal, #24776d)','stroke-width':'2.5'}));
  const guide=el('path',{fill:'none',stroke:'var(--amber, #b0782e)','stroke-width':'1.1','stroke-dasharray':'4 4'});
  const dot=el('circle',{r:5.5,fill:'var(--amber, #b0782e)',stroke:'var(--paper, #fff)','stroke-width':'2'});svg.append(guide,dot);
  svg.append(el('text',{x:494,y:256,'text-anchor':'end',fill:'var(--ink, #222)','font-size':'13'},kind==='growth'?'ε':'y₁'),el('text',{x:51,y:14,fill:'var(--ink, #222)','font-size':'13'},kind==='growth'?'1 / ε':'y₂'));
  function update(){const t=10**Number(slider.value),u=1/t;dot.setAttribute('cx',X(t));dot.setAttribute('cy',Y(u));guide.setAttribute('d',`M${X(t)} ${y0}V${Y(u)}H${x0}`);values.textContent=kind==='growth'?`ε = ${t.toFixed(3)}   ·   f = ${u.toFixed(2)}`:`y₁ = ${t.toFixed(3)}   ·   y₂ = ${u.toFixed(2)}   ·   P = ${(t*t).toFixed(4)}`;slider.setAttribute('aria-valuetext',t.toFixed(3));}
  slider.addEventListener('input',update);update();
  box.append(html('small',{class:'figure-meta'},'Numerical illustration · logarithmic parameter slider · awaiting author review'));
  if(!popout){const button=html('button',{type:'button',class:'text-button'},'Enlarge illustration ↗');box.append(button);button.onclick=()=>{const dialog=html('dialog',{class:'figure-popout'});const close=html('button',{type:'button',class:'text-button'},'Close ×');dialog.append(close);document.body.append(dialog);close.onclick=()=>dialog.close();dialog.addEventListener('close',()=>dialog.remove());draw(dialog,figure,kind,true);dialog.showModal();};}
 }
 window.PAPER_FIGURES={growth:(host,figure)=>draw(host,figure,'growth'),nonattainment:(host,figure)=>draw(host,figure,'nonattainment')};
})();
