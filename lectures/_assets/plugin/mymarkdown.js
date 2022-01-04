(function() {
var renderer = new this.marked.Renderer();
renderer.rimage = renderer.image;

var mermaidCounter = 0

/** rendering mermaid code */
renderer.rcode = renderer.code;
/* renderer.code=function( code,  infostring,  escaped) { 
	// console.log("code("+code+","+infostring+","+escaped+")"); 
	if (infostring==="mermaid") {
		const b64 = btoa(code)
		const imgURL = "https://mermaid.ink/svg/"+b64

		//mermaidCounter++
		//return mermaid.render('mermaid'+mermaidCounter,code)
		return '<img src="'+imgURL+'" class="mermaidgraph" />'
	}
	if (infostring==="dot") {
		var r = ""
		try {
			const svg = Viz(code)
			const offset = svg.indexOf("<svg ")		
			r=svg.substr(offset)
		} catch (error) {
			r= "<div class='error'>failed rendering dot graph: "+error+"</div>"
		}
		return r
	}
	return renderer.rcode(code,infostring,escaped)
}; */

renderer.code=function( code,  infostring,  escaped) { 
	// console.log("code("+code+","+infostring+","+escaped+")"); 
	if (infostring==="mermaid") {
		mermaidCounter++
		return mermaid.render('mermaid'+mermaidCounter,code)
	}
	return renderer.rcode(code,infostring,escaped)
};

/** fit option for headings */
const _heading = function(text, level, _class, raw, slugger) {
  var _classStr = ""
  if (_class && _class!=="")
  	_classStr=' class="' + _class+'"'
  var id = ""
  if (slugger)
  	id = ' id="'
      + slugger.slug(raw)
      + '"'
  return '<h'
      + level
      + id
      +_classStr+'>'
      + text
      + '</h'
      + level
      + '>\n';
};
renderer.heading=function( a,  b,  c, d) { 
	var _class=""
	if (a.includes("<!-- fit"))
		_class="responsive_headline"
	return _heading(a,b,_class,c,d)
};

// renderer.blockquote=function( quote) { console.log("blockquote("+quote+")");};
renderer.html=function( html) { 
	// console.log("html("+html.trim()+")"); 
	if (html.trim() == "<!-- colstart -->")
		return '<div class="container"><div class="col">'
	if (html.trim() == "<!-- col -->" || html.trim() == "<!-- split -->")
		return '</div><div class="col">'
	if (html.trim() == "<!-- colend -->")
		return '</div></div>'
	if (html.trim() == "<!-- references -->")
		return '<div class="stretch"></div><div class="references">'
	if (html.trim() == "<!-- discussion -->")
		return '<img src="./../_assets/_assets/img/discussion.jpg" alt="Discussion" />'
	return html
};

renderer.rlistitem=renderer.listitem
renderer.listitem= function(text, task, checked) {
	if (text.trim()==="")
		return "<li class='hidden'></li>" 
	return renderer.rlistitem(text, task, checked)
}

this.marked.setOptions({renderer:renderer})
// console.log(this.marked.defaults)

const _marked = this.marked
this.marked = function(x, opt, cb) { 
	var pre=post=""
	if (/<!--[^-]*\Wsmall\W[^-]*-/.test(x)) {
		pre = pre + "<div class='small'>"
		post = "</div>"+post
	}
	if (/<!--[^-]*\Wsmaller\W[^-]*-/.test(x)) {
		pre = pre + "<div class='smaller'>"
		post = "</div>"+post
	}
	if (/<!--[^-]*\Wsmallish\W[^-]*-/.test(x)) {
		pre = pre + "<div class='smallish'>"
		post = "</div>"+post
	}
	if (/<!--[^-]*\Wsplit\W[^-]*-/.test(x)) {
		pre = pre + "<div class='container'><div class='col'>"
		post = "</div></div>"+post
	}
	if (/<!-- references -->/.test(x)) {
		post = "</div>"+post
	}
	if (/<!--[^-]*\Wleft\W[^-]*-/.test(x)) {
		pre = pre + "<div class='left'>"
		post = "</div>"+post
	}
	if (/<!--[^-]*\Wright\W[^-]*-/.test(x)) {
		pre = pre + "<div class='right'>"
		post = "</div>"+post
	}

	return pre+_marked(x,opt,cb)+post
}
this.marked.setOptions = function(x) {
	_marked.setOptions(x)
}
	

})();
