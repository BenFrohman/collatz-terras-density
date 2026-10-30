# Terras density

<!-- ZENODO-PROVENANCE-HEADER -->
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23629484.svg)](https://doi.org/10.5281/zenodo.23629484)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)

> **Author:** Benjamin Stanley Frohman ([ORCID: 0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))  
> **Origin Provenance:** `2026-10-04 15:45:31 CDT (Git Initial Commit)`  
> **Zenodo Archive & DOI:** [`10.5281/zenodo.23629484`](https://doi.org/10.5281/zenodo.23629484) ([Zenodo Record `23629484`](https://zenodo.org/records/23629484))  
> **Primary Manuscript PDF:** [`Frohman_Collatz_Terras_Density_Lean4_2026.pdf`](./Frohman_Collatz_Terras_Density_Lean4_2026.pdf)  
> **Copyright & License:** Copyright (c) 2026 Benjamin Stanley Frohman. Licensed under the Apache License, Version 2.0 ([`LICENSE`](./LICENSE), [`NOTICE`](./NOTICE)).
<!-- /ZENODO-PROVENANCE-HEADER -->


Copyright (c) 2026 Benjamin Stanley Frohman.

This repository contains one equation: finite stopping time has density one.

`FiniteStoppingTime n` is `exists k, iter k n < n`.

`binomial_tail` counts bad parity words. It does not say every positive integer reaches 1.

The covering claim is not proved here; it lives in `collatz-covering-claim`. It appears only as the named hypothesis `RemainingLemma` (open; equivalent to Collatz), taken as an explicit argument by `covering_from_assumption` and `density_from_assumption`.

`lake build` is clean: 0 `sorry`, no custom axioms, and all 27 theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

## License

Copyright (c) 2026 Benjamin Stanley Frohman. Licensed under the Apache License, Version 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
