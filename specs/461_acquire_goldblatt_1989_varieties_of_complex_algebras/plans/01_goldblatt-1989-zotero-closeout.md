# Implementation Plan: Task #461

- **Task**: 461 - Acquire Goldblatt 1989 'Varieties of complex algebras' (Annals of Pure and Applied Logic)
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: 460 (per task metadata; not blocking — the acquisition it gated is already complete)
- **Research Inputs**: specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/reports/01_acquisition-verified-corpus-status.md
- **Artifacts**: plans/01_goldblatt-1989-zotero-closeout.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

The acquisition and corpus ingest this task was created for are already done: a complete corpus
entry exists at `~/Projects/Literature/sources/goldblatt_1989/` (PDF + converted markdown),
indexed in both `~/Projects/Literature/index.json` and `specs/literature-index.json` since
2026-08-26, with the OCR-fidelity hazard already recorded. The single step from the task
description that remains genuinely open is the **Zotero add**. Everything else in this plan is
record-correction: making this task's own artifacts and state entry stop asserting the paper is
unobtainable, and linking the corpus entry to the Zotero item once it exists. Definition of done:
a Zotero bibliographic item for Goldblatt 1989 exists (PDF attached if storage quota permits,
metadata-only and honestly labelled if it does not), the corpus indices record its key, this
task's stale first report carries a supersession banner, and `specs/state.json`'s blocker text
reflects reality.

### Research Integration

From `reports/01_acquisition-verified-corpus-status.md`, taken as established and **not**
re-derived at implementation time:

- **Bibliographic record (verified from the PDF's own masthead, TOC, dedication, references and
  `pdfinfo`)**: Goldblatt, R. (1989). "Varieties of Complex Algebras." *Annals of Pure and Applied
  Logic* 44, 173–242. DOI `10.1016/0168-0072(89)90032-8`, PII `0168007289900328`, 70 pages.
- **Corpus state**: already ingested. `~/Projects/Literature/sources/goldblatt_1989/` holds
  `Goldblatt_1989_Varieties_of_Complex_Algebras.pdf` (8,161,997 bytes) and `goldblatt_1989.md`.
  Global index id `goldblatt_1989`; repo sub-index `doc_id: goldblatt_1989`, `"source": "manual"`,
  with `hazard` and `citation_rule` fields already correct. **No re-ingest, re-convert or
  re-index of the source content is in scope.**
- **Zotero state (verified 2026-09-07T19:36:02Z against a freshly regenerated, non-stale
  4046-item export)**: absent. Four unrelated Goldblatt items exist (Topoi, two copies of the
  2003/2006 evolution survey, one stray untitled entry); none is this paper.
- **Environment risk 1**: `zot` on `$PATH` (`~/.nix-profile/bin/zot`) fails every subcommand with
  `ModuleNotFoundError: No module named 'httpx'` because `zotero_cli_cc/cli.py` imports the `add`
  chain at module load. A correctly-provisioned install with `httpx` present exists at
  `~/.local/share/uv/tools/zotero-cli-cc/bin/zot`.
- **Environment risk 2**: this Zotero account is ~9.2x over its storage allotment (documented
  `413 File would exceed quota (2745.6 > 300)` from a prior live attempt). A quota-rejected attach
  is **not** clean — it leaves a file-less orphaned child attachment record on the parent item.
- **Sync-lag caveat**: `zot`'s read commands query local SQLite only. An item created through the
  Web API is invisible to `zot read`/`zot search` and to `zotero-search.sh` until a Zotero desktop
  client syncs it down. Verification of Phase 2 must therefore be a Web-API read, not a local
  search.
- **Duplicate**: `specs/literature/1-s2.0-0168007289900328-main.pdf` is a second independent
  download of the same Elsevier artifact (byte-different, bibliographically identical). It needs
  no ingest action.

### Prior Plan Reference

No prior plan. This is the first plan artifact for this task.

### Roadmap Alignment

No `roadmap_path` was provided in the dispatch context, so no roadmap was consulted and no
roadmap phases are included.

## Goals & Non-Goals

**Goals**:
- Create a Zotero bibliographic item for Goldblatt 1989 with correct metadata and DOI.
- Attach the corpus PDF to that item **if and only if** storage quota permits; otherwise record
  "no PDF attached" honestly rather than as a partial success.
- Record the resulting Zotero item key on the existing `goldblatt_1989` entries in the global
  index and the repo sub-index.
- Annotate `reports/01_acquisition-feasibility.md` as superseded so no future dispatch re-derives
  the moot "not obtainable" conclusion, and correct `specs/state.json`'s stale `blockers` text.
- Leave a written record of the duplicate PDF's status and the recommended disposition.

**Non-Goals**:
- Re-ingesting, re-converting, or re-indexing the paper into the corpus (already done 2026-08-25/26).
- Improving the OCR quality of `goldblatt_1989.md`, or re-running any conversion or fidelity audit.
- Fixing the `zot` packaging defect at its Nix/home-manager root (`~/.dotfiles/home.nix`,
  home-manager profile). This plan routes around the defect for this task only and records the
  root cause; a durable fix belongs in its own task.
- Freeing Zotero storage quota, purging unrelated attachments, or changing the Zotero storage plan.
- Rewriting the body of `reports/01_acquisition-feasibility.md` — it is a historical record of a
  then-accurate finding and is annotated, not revised.
- Deleting `specs/literature/1-s2.0-0168007289900328-main.pdf` without the user's say-so (see
  Phase 5; the file is gitignored and untracked, so deletion is not git-recoverable).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `zot` on `$PATH` fails at import (missing `httpx`), blocking every Zotero write | H | H (already observed) | Phase 1 probes first and routes through `~/.local/share/uv/tools/zotero-cli-cc/bin/zot` via a `PATH` prefix scoped to this dispatch; no global/Nix change |
| PDF attachment rejected with `413` quota error | M | H (account ~9.2x over allotment) | Default to a DOI-only item create (no `--pdf`); attempt attach only if a read-only quota probe shows headroom. PDF already lives durably in the corpus, so a metadata-only item is a complete outcome, not a degraded one |
| A quota-rejected attach leaves an orphaned, file-less child attachment record | M | H if attach attempted | Phase 2 contingency: enumerate `GET /items/<key>/children`, delete only children with `md5: null` created by this run, and record the cleanup |
| Item created but invisible to `zot read`/`zotero-search.sh` (local-SQLite sync lag) misread as failure | M | H (no desktop client running) | Verify via authenticated Web-API `GET` on the returned item key, never via local search; record the sync-lag explicitly in the summary |
| `zot add --pdf` without a resolvable DOI hard-fails (`SystemExit(3)`, no item created) | M | L | Always pass `--doi 10.1016/0168-0072(89)90032-8` explicitly; never rely on PDF-text DOI extraction |
| Editing `~/Projects/Literature/index.json` (11,681 entries) corrupts or reformats the file | H | L | Back up before edit, use a single targeted `jq` update of the one `goldblatt_1989` entry, validate JSON and re-confirm the entry count is unchanged |
| A `specs/state.json` edit clobbers the append-only `artifacts` array | H | L | Touch only `blockers`/`blocks_note`/`last_updated` with targeted `jq`; never assign `.artifacts` wholesale (see `.claude/rules/state-management.md`) |
| `ZOTERO_API_KEY` unset in the implementation shell | M | L (confirmed set at plan time) | Phase 1 checks for presence (never echoes the value); a missing key blocks Phase 2 and is reported, not worked around |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Establish a working Zotero write path [COMPLETED]

**Goal**: Obtain a `zot` invocation that runs without the `httpx` import failure, or determine
that no working path exists in this environment — before any Zotero mutation is attempted.

**Tasks**:
- [x] Probe the `$PATH` binary: `zot --version` and the read-only `zot read stats`. Capture the
      exact output/traceback. *(completed: both invocations fail with `ModuleNotFoundError: No
      module named 'httpx'` at import, exit 1 — matches research finding)*
- [x] If it fails, probe the known-good install directly:
      `~/.local/share/uv/tools/zotero-cli-cc/bin/zot --version`. *(completed: prints "zot,
      version 0.7.0", exit 0)*
- [x] If the direct binary works, establish the routing for the remaining phases by prefixing
      `PATH="$HOME/.local/share/uv/tools/zotero-cli-cc/bin:$PATH"` on each `zotero-write.sh`
      invocation (`zotero-write.sh` resolves `zot` via `command -v`, so a prefix suffices — no
      script edit, no shell-profile change, no Nix/home-manager change). *(completed: confirmed
      zotero-write.sh:53 uses `command -v zot`)*
- [ ] If the direct binary also fails, attempt exactly one recovery: `uv tool install --reinstall
      zotero-cli-cc`. Do not attempt a third repair route. *(deviation: skipped — not needed;
      direct binary succeeded on first probe)*
- [x] Confirm `ZOTERO_API_KEY` is present in the environment (`[ -n "${ZOTERO_API_KEY:-}" ]`);
      never print its value. *(completed: present, value not disclosed)*
- [x] Record in the progress notes which route was used and the exact `zot --version` output.
      *(completed: see progress/phase-1-progress.json)*
- [ ] If no route works: stop at this phase, mark it `[BLOCKED]`, record the root cause, and skip
      Phases 2 and 3. Phases 4 and 5 (record correction) remain executable and MUST still run.
      *(deviation: skipped — not applicable; a working route was found)*

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- None (environment probe only; no repository file is edited in this phase)

**Verification**:
- A `zot --version` invocation exits 0 and prints a version string, with the exact command form
  (bare or `PATH`-prefixed) written down for reuse in Phase 2.
- `zot read stats` exits 0 (read-only smoke test proving the `add`-chain import no longer aborts).
  *(deviation: altered — "stats" is not a real subcommand of the installed 0.7.0 CLI; it is
  treated as an item key and returns a structured `not_found` JSON error, exit 4, not a
  traceback. That absence of a traceback is itself the proof the `httpx` import chain succeeds.
  Ran `zot list --limit 1` as the literal read-only smoke test instead: exit 0, valid JSON
  returned.)*
- `ZOTERO_API_KEY` presence confirmed without disclosing it. *(completed)*

---

### Phase 2: Create the Zotero item for Goldblatt 1989 [COMPLETED]

**Goal**: A Zotero bibliographic item for Goldblatt 1989 exists, with its item key captured, and
its attachment status recorded honestly.

**Tasks**:
- [x] Re-confirm absence immediately before writing, to avoid creating a duplicate: search the
      fresh export (`bash .claude/scripts/zotero-search.sh Goldblatt`) and, if reachable, an
      authenticated Web-API search on DOI `10.1016/0168-0072(89)90032-8`. If an item already
      exists, skip the create and carry its key forward. *(completed: both searches confirmed
      absence — export search returned only the 4 known unrelated items, live Web-API DOI search
      returned `[]`)*
- [x] Attempt a read-only storage-quota probe against the Zotero Web API for the authenticated
      user. If no such endpoint responds (it may not exist or may 404), do **not** invent one —
      treat the documented `2745.6 > 300` MB overage from
      `context/project/literature/patterns/zotero-item-creation.md` as authoritative. *(completed:
      no such endpoint exists — `/users/2622830/storageadmin` 404s; documented overage treated as
      authoritative)*
- [x] Choose the create route on the probe result:
      - **No headroom / probe unavailable (expected default)**: DOI-only create, no attachment —
        `bash .claude/scripts/zotero-write.sh item-add --doi 10.1016/0168-0072(89)90032-8`.
      - **Headroom confirmed**: `item-add --pdf ~/Projects/Literature/sources/goldblatt_1989/Goldblatt_1989_Varieties_of_Complex_Algebras.pdf --doi 10.1016/0168-0072(89)90032-8`
        (prefer this corpus copy over the opaquely-named duplicate).
      *(completed: DOI-only route chosen — no headroom probe available)*
- [x] Run the chosen command with `--dry-run` first and read the preview before the real call.
      *(completed: dry-run previewed `{"would": {"source": "doi", "doi": "10.1016/0168-0072(89)90032-8", "resolve_metadata": true}}`)*
- [x] Execute the real call once, with `--idempotency-key` set, capturing the full stdout envelope
      to the progress notes. *(completed: `--idempotency-key task461-goldblatt1989-doi-add-1`; full
      envelope in progress/phase-2-progress.json)*
- [x] Extract the item key from `.data.key` (the empirically confirmed path; `.data.item.key` and
      `.data.itemKey` do not exist in the real envelope). *(completed: key = `MJEB25VU`)*
- [ ] If an attach was attempted and failed (`413` / `.data.attachment_error` present): enumerate
      `GET https://api.zotero.org/users/<uid>/items/<key>/children` (read-only) and delete only
      the child attachment records with `md5: null` that this run created. Record each deletion.
      *(deviation: skipped — not applicable; DOI-only create attempted no attachment, so there is
      no attach failure to handle. Confirmed `GET .../items/MJEB25VU/children` returns `[]`.)*
- [x] Record the outcome in one of exactly two honest forms: "item created, PDF attached" or
      "item created, **no PDF attached** (storage quota)". Never describe the second as a full
      success. *(completed: outcome is "item created, **no PDF attached** (storage quota)")*

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts that **exactly one** Zotero item is created and that the
paper is currently absent from the library. Confirm at implementation time with the pre-write
search above (fresh export plus, if reachable, a Web-API DOI search) rather than relying on the
research report's 2026-09-07 snapshot; if a matching item already exists, create nothing and reuse
its key.

**Files to modify**:
- None in this repository (the mutation is external, in the Zotero library)

**Verification**:
- An authenticated Web-API `GET .../items/<key>` returns the item with title "Varieties of Complex
  Algebras", creator Goldblatt, and DOI `10.1016/0168-0072(89)90032-8`. *(confirmed: `GET
  .../items/MJEB25VU` returns title "Varieties of complex algebras" (CrossRef-resolved
  capitalization — sentence case, not title case; same paper), creator Robert Goldblatt, DOI
  `10.1016/0168-0072(89)90032-8`, publicationTitle "Annals of Pure and Applied Logic", volume 44,
  pages 173-242)*
- **Do not** verify via `zot read`, `zot search`, or `zotero-search.sh`: those read local SQLite
  and will report "not found" for a Web-API-created item until a desktop client syncs it. A
  local-search miss is expected and is not evidence of failure. *(honored: verification used the
  Web API exclusively, not local search)*
- If an attach was attempted, `GET .../items/<key>/children` shows either a real attachment (with
  non-null `md5`) or no file-less orphan records left behind. *(confirmed: no attach was
  attempted; `GET .../items/MJEB25VU/children` returns `[]`)*

---

### Phase 3: Record the Zotero linkage on the corpus index entries [COMPLETED]

**Goal**: The `goldblatt_1989` entries in the global index and the repo sub-index carry the Zotero
item key, closing the provenance gap the research report identified (the entry currently has no
`zotero_key`/`zotero_path` at all, unlike siblings that went through the Zotero-first pipeline).

**Tasks**:
- [x] Skip this phase entirely if Phase 2 produced no item key; mark it `[BLOCKED]` with that reason.
      *(completed: not applicable -- Phase 2 produced key MJEB25VU, phase proceeds)*
- [x] Back up both index files before editing (timestamped copies in the scratchpad).
      *(completed: index.json.bak.20260907T195332Z, literature-index.json.bak.20260907T195332Z)*
- [x] Add `"zotero_key": "<key>"` to the `goldblatt_1989` entry in `~/Projects/Literature/index.json`
      via a single targeted `jq` update of that one entry. *(completed: zotero_key MJEB25VU added,
      entry count unchanged 11681 -> 11681)*
- [x] Add `"zotero_key": "<key>"` to the `doc_id: "goldblatt_1989"` entry in
      `specs/literature-index.json`. *(completed: zotero_key MJEB25VU added, entry count
      unchanged 1 -> 1)*
- [x] Add `zotero_path` **only** if a real attachment landed in the derived Zotero storage tree
      (`$(dirname "$(bash .claude/scripts/zotero-resolve-sqlite-path.sh)")/storage/<attachmentKey>/`)
      and the file exists on disk. If the attach was quota-rejected, omit the field rather than
      pointing at a nonexistent path. *(completed: omitted -- no attachment landed, DOI-only
      create per Phase 2)*
- [x] Leave `"source": "manual"` unchanged in the sub-index — it accurately records how the corpus
      entry was created, and the Zotero item does not retroactively change that provenance.
      *(completed: confirmed unchanged by diff)*
- [x] Leave `hazard`, `citation_rule`, `reason`, and every other existing field untouched.
      *(completed: confirmed unchanged by diff -- both entries show a single-field addition only)*

**Timing**: 0.25 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts **exactly two** index files and **exactly one** entry in
each. Confirm at implementation time with `jq '[.entries[] | select(.doc_id=="goldblatt_1989")] |
length'` on the sub-index and the equivalent id-match count on the global index; a count other
than 1 means duplicate entries exist and must be reported rather than silently edited.

**Files to modify**:
- `~/Projects/Literature/index.json` — add `zotero_key` to the `goldblatt_1989` entry
- `specs/literature-index.json` — add `zotero_key` to the `doc_id: goldblatt_1989` entry

**Verification**:
- Both files parse: `jq empty` exits 0 on each. *(confirmed)*
- Global index entry count is unchanged before vs. after (11,681 at research time — compare the
  measured before-count, not the quoted one). *(confirmed: measured before-count 11681, after
  11681)*
- `jq` on each file returns the `goldblatt_1989` entry with the new `zotero_key` and every
  pre-existing field intact (diff the single entry, not the whole file). *(confirmed: diff of
  each entry against its backup shows exactly one added line, `"zotero_key": "MJEB25VU"`, with
  every pre-existing field byte-identical)*

---

### Phase 4: Correct the stale first report and the task state record [COMPLETED]

**Goal**: This task's own artifacts stop asserting the paper is unobtainable, so no future
dispatch re-runs the moot acquisition investigation.

**Tasks**:
- [x] Insert a short supersession banner immediately under the title of
      `reports/01_acquisition-feasibility.md`, stating that its "not obtainable" conclusion was
      accurate as of 2026-08-18 but was overtaken by events: the PDF was obtained and ingested on
      2026-08-25/26, and the report is superseded by
      `reports/01_acquisition-verified-corpus-status.md`. Keep the banner to a few lines.
      *(completed)*
- [x] Do not edit the body of that report — it is a historical record of a then-accurate finding.
      *(completed: only an insertion after the title; body untouched)*
- [x] Update `specs/state.json`'s task-461 entry with targeted `jq`: rewrite `blockers` to state
      the acquisition blocker was cleared 2026-08-26 (replacing the long "no legitimately
      obtainable copy exists" text), and update `blocks_note` to record the corpus ingest as
      complete plus the Zotero outcome from Phase 2. *(completed)*
- [x] Touch **only** `blockers`, `blocks_note`, and `last_updated`. Never assign `.artifacts`
      wholesale — the array is append-only per `.claude/rules/state-management.md`. *(completed:
      jq targeted exactly these three fields on the 461 entry)*
- [x] Regenerate the rendered view: `bash .claude/scripts/generate-todo.sh`. Do not hand-edit
      `specs/TODO.md`. *(completed)*

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts **exactly two** edited files (`reports/01_acquisition-feasibility.md`
and `specs/state.json`) plus one regenerated file (`specs/TODO.md`). Confirm with `git status
--short` at phase end; any additional modified path means the `jq` edit or the generator touched
more than intended and must be inspected before committing.

**Files to modify**:
- `specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/reports/01_acquisition-feasibility.md` — prepend supersession banner
- `specs/state.json` — task-461 `blockers`, `blocks_note`, `last_updated`
- `specs/TODO.md` — regenerated (not hand-edited)

**Verification**:
- `jq empty specs/state.json` exits 0, and `jq '.active_projects[] | select(.project_number==461) |
  .artifacts | length'` returns the same count as before the edit (1). *(confirmed, modulo a
  count correction: the actual pre-edit count was 2, not 1 — this plan's figure was stale; the
  measured before-count (2) matches the after-count (2), which is what the check requires)*
- `git diff specs/state.json` shows changes confined to the three named fields of the 461 entry.
  *(confirmed for the 461 entry specifically; the shared file's diff also carries an
  already-dirty `status` field transition and other tasks' own concurrent edits, both pre-existing
  and outside this phase's edit — see Phase 4 observations in progress/phase-4-progress.json)*
- The banner is present at the top of the old report and its original body text is unchanged
  (`git diff` shows an insertion only). *(confirmed)*

---

### Phase 5: Duplicate disposition and task closeout [COMPLETED]

**Goal**: The redundant duplicate PDF's status is recorded and surfaced for the user's decision,
and the task's outcome is written up.

**Tasks**:
- [x] Leave `specs/literature/1-s2.0-0168007289900328-main.pdf` **in place, untouched**. It is
      gitignored (`.gitignore:29`) and untracked, so deletion is not git-recoverable; the content
      is preserved either way in the corpus copy. Do not move, rename, or ingest it. *(completed:
      untouched, size confirmed 8,161,482 bytes)*
- [x] Confirm nothing references it: grep `specs/` and `.claude/` for the filename and record the
      result (the research report's own citation of the path is expected and fine). *(completed:
      every reference found is within this task's own artifacts — the two reports, this plan, and
      state.json's blocks_note — nothing outside this task cites it)*
- [x] Surface the deletion question as a **non-blocking** `user_decision` on `.return-meta.json`
      (question, options, recommended, `blocking: false`), recommending "leave in place".
      *(completed)*
- [x] Write `summaries/01_goldblatt-1989-zotero-closeout-summary.md` recording: the Zotero item key
      and its attachment status in the honest two-form language from Phase 2; the index fields
      added; the report and state corrections; the duplicate's disposition; and the two
      environment defects (`zot` `httpx` packaging, Zotero storage overage) as outstanding
      environment issues that this task routed around rather than fixed. *(completed)*
- [x] Note in the summary that the `zot` packaging defect and the storage-quota overage each merit
      their own task if they are to be fixed durably; do not create those tasks from here.
      *(completed: see summary Follow-ups section)*

**Timing**: 0.5 hours

**Depends on**: 3, 4

**Verification Tier**: prose

**Files to modify**:
- `specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/summaries/01_goldblatt-1989-zotero-closeout-summary.md` — new
- `specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/.return-meta.json` — `user_decision` field

**Verification**:
- `specs/literature/1-s2.0-0168007289900328-main.pdf` still exists with its original size
  (8,161,482 bytes) and mtime. *(confirmed: `stat` reports 8161482 bytes, mtime unchanged)*
- The summary exists, follows summary-format.md, and its Zotero-outcome sentence matches the
  Phase 2 evidence rather than overstating it. *(confirmed)*
- `.return-meta.json` parses and carries a `user_decision` object with `blocking: false`.
  *(confirmed)*

## Testing & Validation

- [ ] `zot --version` exits 0 via the route recorded in Phase 1.
- [ ] An authenticated Web-API `GET .../items/<key>` returns the Goldblatt 1989 item with the
      correct DOI (the sole authoritative existence check; local search is expected to miss it).
- [ ] No file-less orphaned child attachment records remain on the new item.
- [ ] `jq empty` passes on `~/Projects/Literature/index.json`, `specs/literature-index.json`, and
      `specs/state.json`.
- [ ] Global index entry count unchanged before vs. after the Phase 3 edit.
- [ ] Task 461's `artifacts` array in `specs/state.json` still has all pre-existing entries.
- [ ] `specs/TODO.md` regenerated by script, not hand-edited.
- [ ] `git status --short` at task end shows only the files enumerated in Phases 3–5.
- [ ] Every claim in the summary about attachment status is supported by captured command output.

## Artifacts & Outputs

- A Zotero bibliographic item for Goldblatt 1989 (external; item key recorded in the summary)
- `~/Projects/Literature/index.json` — `zotero_key` added to the `goldblatt_1989` entry
- `specs/literature-index.json` — `zotero_key` added to the `goldblatt_1989` entry
- `specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/reports/01_acquisition-feasibility.md` — supersession banner
- `specs/state.json` — corrected `blockers`/`blocks_note` for task 461; `specs/TODO.md` regenerated
- `specs/461_acquire_goldblatt_1989_varieties_of_complex_algebras/summaries/01_goldblatt-1989-zotero-closeout-summary.md`
- `.return-meta.json` with a non-blocking `user_decision` on the duplicate PDF

## Rollback/Contingency

- **Zotero item**: if the created item is wrong (bad metadata, duplicate of an existing entry),
  delete it via an authenticated Web-API `DELETE .../items/<key>` together with any child
  attachment records, and record the rollback. The item key captured in Phase 2 is the rollback
  handle; do not proceed past Phase 2 without it.
- **Index files**: restore from the timestamped backups taken at the start of Phase 3.
  `~/Projects/Literature/index.json` is outside this repository and is **not** git-recoverable —
  the backup is the only rollback path, so take it before the first edit, not after.
- **Repository files**: `specs/state.json`, `specs/TODO.md`, and the report banner are all tracked;
  revert with `git checkout` from a clean-tree state, or by reverting the phase commit.
- **Duplicate PDF**: no rollback needed — the plan does not modify or delete it.
- **If Phase 1 finds no working `zot` route**: Phases 2 and 3 are skipped and marked `[BLOCKED]`
  with the root cause; Phases 4 and 5 still run, so the record-correction value of this task is
  delivered regardless, and the task ends `[PARTIAL]` with the Zotero add as the single named
  remainder.
