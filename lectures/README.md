# Lecture Slides

This folder contains lecture slides for 17-445/645. Feel free to contribute to the slides through pull requests -- from fixing small issues to new discussions or case studies, pull requests from students, instructors, and other interested parties are certainly welcome.

The rendered versions of these slides can be found at https://ckaestne.github.io/seai/slides/

## Slide format and infrastructure

Slides are written in markdown, one slidedeck per folder, and converted to slides with a slightly patched version of [reveal-md](https://github.com/webpro/reveal-md)

Each slide deck is in a separate subdirectory. Can use all the usual markdown features of `reveal.js` plus a few custom ones created with scripts in the `_assets` directory.

Basics:
* Formatting, including headers, links, lists, bold font, quotes, and source code can be done as usual in markdown.
* Slide separators are `---` for chapters and `----` for slides within a chapter.
* `Notes:` introduces a part of the slide that is hidden from the presentation but included when printing/in PDFs.
* Frontmatter in yaml format define title, footer, and author.

Custom extensions in `/_assets/plugin/mymarkdown.js`:
* `<div class="small">`, `smaller` and `smallish` can be used to adjust font sizes in a slide
* `<!-- references -->` starts a segment for the bottom of the slide in a smaller font, intended for references and additional readings.
* Explicit column handling, included nested columns and more than two columns, is possible between `<!-- colstart -->` and `<!-- colend -->` with `<!-- col -->` as the separator
* Empty items in a list can be used as a space/separator between two list
* `<!-- discussion  -->` marks the slide as a discussion slide, adding a picture (possibly exploring other design features later)

Other useful suggestions:
* `<!-- .element: class="stretch" -->` is a useful extension for figures that should stretch to the remainder of the page (add in new line after image)
* Let's use links when referencing sources 
* Use chapters with `#` headings (separated by `---`) and slides with `##` headings within a chapter (separated by `----`), turning into horizontal and vertical navigation in the final presentation

## Editing

Run `reveal-md . --watch` to run a local webserver that shows the slides and automatically updates on changes to the .md files. (Run `npm install` first to install the dependencies locally)

## Static sites and circle-CI automation

To produce static slides, run `reveal-md . --static`. The slides will be created in the `_static` directory. Circle-ci automates the process and pushes the results to the `gh-pages` branch, which can be seen at https://ckaestne.github.io/seai/slides/.

