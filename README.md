# abeln.github.io

Abel Nieto's personal site, built with Quartz and published with GitHub Pages.

## Write a note

Create a Markdown file under `content/notes/` and start writing. Frontmatter is optional. For a convenient starter:

```sh
./scripts/new-note "My note title"
```

Add metadata only when it is useful:

```yaml
---
tags:
  - math/category-theory
---
```

## Preview

Quartz requires Node.js 22 or newer.

```sh
npm install
npm run quartz -- build --serve
```

Open <http://localhost:8080>. The preview reloads as Markdown files change.

## Publish

Commit and push to `master`. The GitHub Pages workflow builds and deploys the site automatically.
