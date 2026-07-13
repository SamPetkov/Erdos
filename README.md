# Erdős problem research

<p align="center">
  <a href="625/">
    <img src="625/assets/erdos625-preview.png" alt="Schematic overview of Erdős Problem 625, its graph parameters, and the proposed lower bound" width="1100">
  </a>
</p>

<p align="center"><em>Problem 625 at a glance. This diagram is an explanatory preview, not part of the proof or its verification.</em></p>

## Animated exact example

<p align="center">
  <a href="625/assets/animations/erdos625-coloring-example.mp4">
    <img src="625/assets/animations/erdos625-coloring-example.gif" alt="Animated exact coloring and cochromatic partition of a fixed 12-vertex graph" width="960">
  </a>
</p>

<p align="center"><em>A selected, exactly solved 12-vertex illustration. Click for MP4. The seed was chosen to explain the parameters; it is not representative, statistical, or asymptotic proof evidence.</em></p>

This repository collects research dossiers on individual Erdős problems.
Each numbered directory is intended to be self-contained and keeps its proof,
audits, literature ledger, reproducibility code, and verification records
together.

## Available dossiers

- [Problem 625](625/) — a proposed positive resolution for the chromatic and
  cochromatic number gap in `G(n,1/2)`, including a self-contained manuscript,
  four full internal audits, a fresh adversarial leap audit with three
  independent regression reviews, synchronized supporting proof components,
  scope-qualified historical audits, an additional provisional verification
  with separately written finite checks, and reproducibility artifacts.

Direct artifacts: [PDF proof](625/output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf),
[TeX source](625/output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex),
[verification record](625/verification/), and
[complete ZIP](625/releases/Erdos-625-complete-dossier-2026-07-13.zip).
The [README GIF](625/assets/animations/erdos625-coloring-example.gif),
[MP4](625/assets/animations/erdos625-coloring-example.mp4), and
[rebuild record](625/assets/animations/) are also available directly.

The Problem 625 argument is new and has not yet undergone external peer
review, publication, or community acceptance.  The repository presents the
proof and its internal checks for expert scrutiny; it does not claim an
official change to the problem's published status.
