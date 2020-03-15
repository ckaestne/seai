echo generate main html page in _site/
mkdir _site
npm install marked
cp .assets/template.html _site/index.html
node_modules/marked/bin/marked -i README.md >> _site/index.html
cat .assets/template_end.html >> _site/index.html
cp *.png _site/
cp *.jpg _site/
