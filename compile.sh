#!/usr/bin/bash

#font_path = "--font-path ./fonts"
font_path = ""

# Turns path of document into a displayable name (just swaps / for - and removes the extension)
function nameof () {
    dashes="${1//\//-}"
    echo "${dashes%.*}"
}

# Collect documents:
#  .typ files that don't contain FLASHBANG IGNORE (explicit) or FLASHBANG INCLUDE (library files not meant to contain cards)
documents=()
while IFS=  read -r -d $'\0'; do
    if ! grep -F -q -e '//![FLASHBANG IGNORE]' -e '//![FLASHBANG INCLUDE]' "$REPLY"; then
        documents+=("$REPLY")
    fi
done < <(find . -name "*.typ" -not -path "./dist/*" -printf "%P\0")
# ^ think of excluding dist

mkdir -p ./dist

src="./dist/_full.typ"
# Regex to recompute paths in the merged file
re="^(.*)import \"(.+)\.typ\"(.*)$"
full="./dist/_full.pdf"

# Merged file header
echo -e "#import \"../cards.typ\": *\n#show: setup" > "$src"

# compile documents, build merged source
for doc in "${documents[@]}"; do

    # start new section (avoid polluting the global scope)
    echo "#[" >> "$src"
    awk '/^\/\/!\[FLASHBANG HEADER\]/{flag=1;next} flag' "$doc" >> "$src"
    echo "]" >> "$src"

    name="$(nameof "$doc")"

    # Compile each file
    >&2 echo "compiling $doc -> ./dist/$name.pdf"
    typst compile --root . "$font_path" --ignore-system-fonts "$doc" "./dist/$name.pdf"
done

# Compile merged file
>&2 echo "compiling $src -> $full"
typst compile --root . "$font_path" --ignore-system-fonts "$src" "$full"

# Build index
cat > ./dist/index.html << EOF
<html>
    <head>
        <title>Flashbang cards</title>
        <meta charset="UTF-8" />
        <style>
            html, body {
                margin: 0;
                padding: 0;
            }

            body {
                display: flex;
                width: 100vw;
                height: 100vh;
                justify-content: center;
                align-items: center;
                flex-direction: column;
                font-size: 2em;
                gap: 1em;
                background: #fafafa;
                font-weight: bold;
            }
            a {
                color: #34abeb;
                text-decoration: none;
            }
        </style>
    </head>
    <body>
        Flashbang cards
        <a href="_full.pdf"> everything </a>
EOF

# Add links to individual files
for doc in "${documents[@]}"; do
    name="$(nameof "$doc")"
    echo "<a href=\"$name.pdf\"> $name </a>" >> ./dist/index.html
done

# Finish index
cat >> ./dist/index.html << EOF
    </body>
</html>
EOF
