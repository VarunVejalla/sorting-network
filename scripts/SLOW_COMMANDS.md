# Slow Commands Log

Track commands that exceeded expected time. Each entry should include:
- Date, command, expected time, actual time
- Root cause (if identified)
- Fix applied (if any)

## Baselines

| Operation | Expected | Notes |
|---|---|---|
| `rg` through Mathlib | ~0.2s | 86MB, 7516 .lean files |
| `mcp__lean__check` warm | 0.2-2s | Persistent lake serve LSP |
| `mcp__lean__check` cold first file | 2-5s | lake serve loading imports |
| Root `lake build` | Cache/package context only | Root Lakefile defines no Lean libraries; build from a proof package instead |
| Package `lake build` (cached) | Varies by package | Run in `upper-bound/best`, `lower-bound/best`, or another package directory |

## Log

(No entries yet)
