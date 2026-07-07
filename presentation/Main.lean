import VersoSlides
import Slides

open VersoSlides

/-- "Query Console" — a fresh editorial theme: warm paper background, a serif/mono
type pairing instead of keynote sans-uppercase, one warm accent color, and code blocks
styled like real terminal windows. Built as an override on top of the light `white`
base theme rather than from scratch, to keep the underlying contrast/accessibility
rules sound. -/
def queryConsoleCss : Verso.Genre.Manual.CSS := Verso.Genre.Manual.CSS.mk r##"
.reveal {
  --r-background-color: #faf6ef;
  --r-main-color: #211c17;
  --r-main-font: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
  --r-main-font-size: 26px;
  --r-heading-font: Georgia, "Times New Roman", ui-serif, serif;
  --r-heading-color: #211c17;
  --r-heading-font-weight: 600;
  --r-heading-text-transform: none;
  --r-heading-letter-spacing: -0.01em;
  --r-heading-line-height: 1.15;
  --r-heading-margin: 0 0 0.35em 0;
  --r-heading1-size: 1.9em;
  --r-heading2-size: 1.35em;
  --r-heading3-size: 1.1em;
  --r-heading4-size: 1em;
  --r-block-margin: 16px;
  --r-link-color: #c9552f;
  --r-link-color-dark: #a3441f;
  --r-link-color-hover: #a3441f;
  --r-selection-background-color: #c9552f;
  --r-selection-color: #fff;
}

.reveal .slides section, .reveal .slides section > * { text-align: left; }
.reveal .slides { text-align: left; }

/* editorial "kicker" label above headings, e.g. `01 · Motivation` */
.kicker {
  display: inline-block;
  font-family: ui-monospace, "SF Mono", Consolas, Menlo, monospace;
  font-size: 0.5em;
  font-weight: 700;
  letter-spacing: 0.08em;
  color: #c9552f;
  vertical-align: middle;
  margin-right: 0.5em;
}

/* `#` headings render as `<h2>` (verso reserves `<h1>` for the document title). */
.reveal .slides section h2::after {
  content: "";
  display: block;
  border-top: 3px solid #c9552f;
  width: 64px;
  margin: 0.3em 0 0.5em 0;
}

/* progress bar + slide number, restyled minimal */
.reveal .progress { color: #c9552f; height: 4px; }
.reveal .slide-number {
  font-family: ui-monospace, monospace;
  font-size: 14px;
  background: transparent;
  color: #a3441f;
  opacity: 0.6;
}

/* code panes as dark terminal cards, regardless of surrounding light theme.
   `!important` is required: the panel JS sets an inline `style="background: ..."`
   on `<pre>` at runtime (a light tint meant for a dark base theme), and inline
   styles otherwise beat any stylesheet rule regardless of selector specificity. */
.reveal pre {
  background: #211c17 !important;
  border-radius: 10px;
  box-shadow: 0 8px 24px rgba(33, 28, 23, 0.18);
  border: 1px solid #3a322a;
}
.reveal pre code {
  font-family: ui-monospace, "SF Mono", Consolas, Menlo, monospace !important;
  font-size: 0.75em;
  line-height: 1.55;
  background: transparent !important;
  /* Fallback for any plain, un-tokenized text. Real syntax-highlighted tokens
     (`.hljs-*` spans from `highlightTheme := .monokai`) are more specific and
     win normally, now that the `<pre>` background above is reliably dark. */
  color: #f7f0e4;
}

/* side-by-side query comparison layout */
.reveal .r-hstack { align-items: stretch; gap: 1em; }
.reveal .r-hstack > * { flex: 1 1 0; min-width: 0; }
.reveal .r-hstack > .equiv-mark {
  flex: 0 0 auto;
  align-self: center;
  font-family: Georgia, serif;
  font-size: 1.8em;
  font-weight: 700;
  color: #c9552f;
  padding: 0 0.1em;
}

/* frame = bordered card, used for callouts and quotes */
.reveal .r-frame {
  display: block;
  border: 1px solid rgba(33, 28, 23, 0.14);
  border-radius: 10px;
  padding: 0.55em 0.8em;
  background: rgba(201, 85, 47, 0.05);
}

/* bullets: a warm arrow instead of a disc */
.reveal ul { list-style: none; padding-left: 0; margin-left: 0; }
.reveal ul li {
  padding-left: 1.3em;
  position: relative;
  margin-bottom: 0.4em;
}
.reveal ul li::before {
  content: "→";
  position: absolute;
  left: 0;
  color: #c9552f;
  font-weight: 700;
}

/* tables restyled to match the palette */
.reveal table { border-collapse: collapse; font-size: 0.72em; margin: 0 auto; }
.reveal table th {
  color: #c9552f;
  border-bottom: 2px solid #c9552f;
  text-align: left;
  padding: 0.35em 0.7em;
  font-family: ui-monospace, monospace;
  font-weight: 700;
}
.reveal table td {
  padding: 0.35em 0.7em;
  border-bottom: 1px solid rgba(33, 28, 23, 0.1);
  vertical-align: top;
}

/* pull quotes */
.reveal blockquote {
  border-left: 3px solid #c9552f;
  padding-left: 0.9em;
  font-style: italic;
  opacity: 0.85;
  font-family: Georgia, serif;
}

/* dark slides: reveal.js auto-tags these `.has-dark-background` by luminance */
.reveal .slides section.has-dark-background,
.reveal .slides section.has-dark-background h1,
.reveal .slides section.has-dark-background h2,
.reveal .slides section.has-dark-background h3,
.reveal .slides section.has-dark-background p,
.reveal .slides section.has-dark-background li {
  color: #faf6ef;
}
.reveal .slides section.has-dark-background .kicker { color: #f2b28f; }
.reveal .slides section.has-dark-background h2::after { border-top-color: #f2b28f; }
.reveal .slides section.has-dark-background ul li::before { color: #f2b28f; }
.reveal .slides section.has-dark-background .r-frame {
  border-color: rgba(250, 246, 239, 0.25);
  background: rgba(250, 246, 239, 0.08);
}
"##

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "white"
      -- The base `white` theme defaults to a *light*-background highlight.js theme
      -- (`.github`), which renders near-invisible dark-gray text against our dark
      -- terminal-style `<pre>` cards. `monokai` is tuned for a dark background.
      highlightTheme := VersoSlides.HighlightTheme.monokai
      slideNumber := true
      transition := "fade"
      width := 1280
      height := 720
      extraCss := #[{ filename := "query-console.css", contents := queryConsoleCss }]
    })
    (doc := %doc Slides)
