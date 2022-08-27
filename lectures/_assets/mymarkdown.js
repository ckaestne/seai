function patchMarkdown(marked) {

	var renderer = new marked.Renderer();
	renderer.rimage = renderer.image;
	console.log("loading mymarkdown.js")

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
		if (html.trim() == "<!-- references_ -->")
			return '<div class="references">'
		if (html.trim() == "<!-- discussion -->")
			return '<img src="../_assets/discussion.jpg" alt="Discussion" />'
		return html
	};

	renderer.rlistitem=renderer.listitem
	renderer.listitem= function(text, task, checked) {
		// console.log(text)
		if (text.trim()==="")
			return "<li class='hidden'></li>" 
		return renderer.rlistitem(text, task, checked)
	}

	// this.marked.setOptions({renderer:renderer})
	// // console.log(this.marked.defaults)

	// const newmarked = function(x, opt, cb) { 
	// 	var pre=post=""
	// 	if (/<!--[^-]*\Wsmall\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='small'>"
	// 		post = "</div>"+post
	// 	}
	// 	if (/<!--[^-]*\Wsmaller\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='smaller'>"
	// 		post = "</div>"+post
	// 	}
	// 	if (/<!--[^-]*\Wsmallish\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='smallish'>"
	// 		post = "</div>"+post
	// 	}
	// 	if (/<!--[^-]*\Wsplit\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='container'><div class='col'>"
	// 		post = "</div></div>"+post
	// 	}
	// 	if (/<!-- references -->/.test(x)) {
	// 		post = "</div>"+post
	// 	}
	// 	if (/<!--[^-]*\Wleft\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='left'>"
	// 		post = "</div>"+post
	// 	}
	// 	if (/<!--[^-]*\Wright\W[^-]*-/.test(x)) {
	// 		pre = pre + "<div class='right'>"
	// 		post = "</div>"+post
	// 	}

	// 	return pre+marked(x,opt,cb)+post
	// }
		
	return renderer
}
