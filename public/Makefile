fb-core := ./src/fb-web/package.json

build: install-npm
	npm run build

wasm-bundle.zip:
	gh release download --repo viandoxdev/flashbang --patern "wasm-bundle.zip"

$(fb-core): wasm-bundle.zip
	rm -rf src/fb-web
	unzip wasm-bundle.zip
	mv pkg src/fb-web

.PHONY: clear-fb-web download-fb-web install-fb-web install-npm run-debug build

clear-fb-web:
	rm -rf ./src/fb-web
download-fb-web: wasm-bundle.zip
install-fb-web: $(fb-core)
install-npm: $(fb-core)
	npm ci

run-debug: install-npm
	npm run dev
