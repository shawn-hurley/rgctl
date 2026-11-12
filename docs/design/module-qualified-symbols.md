# Names for previously unqualified Tier 1 declarations

JavaScript, TypeScript, Python and Go now populate `qualified_name` for declarations
that previously left the field empty. Existing explicitly qualified member names
and language-specific callable discriminators are retained.

For example, `src/app.ts` emits `src.app.exercise` for a top-level `exercise`
function. Nested declarations include their lexical owner. Python package
initializers use the containing package: `pkg/__init__.py` emits `pkg.exercise`.
Go uses the declared package for standalone extraction; repository extraction
includes the logical directory when necessary to distinguish packages with the
same declaration name.

The shared helper runs on the existing extraction worker after the single-pass
walker has produced symbols and relations. It does not parse a second tree or
read package-manager files. The legacy split extraction APIs expose the same
names. Local relation sources and unambiguous target hints are updated together;
ambiguous imported bindings are not guessed.

Standalone absolute paths have no repository context, so JavaScript, TypeScript
and Python use their file stem. The extraction worker rebases generated names
using its repository-relative path. This happens after loading the raw facts
cache as well as after fresh extraction, so identical source bytes reused across
modules or checkout roots do not inherit the first cached module namespace.
Physical checkout paths never become namespace prefixes.

`module_namespace` metadata marks generated names for rebasing. Existing explicit
owner names are not renamed by this migration. This supplies missing names; it
does not implement module loading, import alias resolution, receiver value flow
or runtime dispatch. Graph IDs remain separate from the optional name field.

Facts-cache format 8 and extraction semantics version 11 invalidate older facts
and force graph regeneration rather than mixing old and new symbol identities.

The `module_qualified_names` integration tests cover public API consistency,
matching call endpoints, same-line callers, Python lexical nesting/package
initializers, logical module separation and cache reuse across checkout roots.
