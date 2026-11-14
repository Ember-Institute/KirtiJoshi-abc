# Source attribution and supplied license text

The integration proof bodies are adapted from the heights contributors' source at commit
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The original source headers state:

> Copyright (c) 2026 The heights contributors. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: The heights contributors

Those headers are retained in the adapted Lean files and the full original reference files.
The reference files under `reference/` are byte-identical copies of the supplied heights
archive's `Heights/Different/{Conductor,Bounds,Places,NumberField}.lean`.

Read-only inspection of the supplied `heights.tar.gz`, `belyi.tar.gz`, and `genl.tar.gz`
archives found no entry named LICENSE or NOTICE (including `.txt`/`.md` variants).
The extracted heights checkout also lacks these files. Archive identities, entry counts and
this observed absence are recorded in `INPUT_MANIFEST.json`. The belyi/genl archives are
listed only to document the supplied provenance context; this unit copies no new proof
body directly from them.

The root `LICENSE` is the standard Apache License 2.0 text copied from the local operating
system's `/usr/share/common-licenses/Apache-2.0`. It is supplied as standard license text,
not asserted to be a recovered upstream LICENSE. No upstream NOTICE has been invented.
This attribution file is task-authored provenance documentation, not an upstream NOTICE.

The inherited project definition files are copied under `reference/baseline/` only as
statement witnesses. Their original copyright headers are retained. The unit itself does
not change their definitions. Referenced Mathlib APIs remain in the existing dependency;
Mathlib implementation files are hashed as read-only witnesses, not copied into integration.
