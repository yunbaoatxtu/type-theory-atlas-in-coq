# Type Theory Atlas in Coq

## Overview

Type Theory Atlas in Coq formalizes a shared framework for MLTT, UTT, and
TDTT, then connects the systems through translations and reusable metatheory
certificates. The development follows the staged route requested for the
automation: unified syntax framework, MLTT, UTT, TDTT, system translations, and
metatheory.

Current top-level entry points:

- public release paper route:
  `type_theory_atlas_public_release_paper_route_holds`;
- public release complete:
  `type_theory_atlas_public_release_complete_holds`;
- public release paper route certificate:
  `type_theory_atlas_public_release_paper_route_certificate_holds`;
- public release complete certificate:
  `type_theory_atlas_public_release_complete_certificate_holds`;
- public release manifest:
  `type_theory_atlas_public_release_manifest_holds`;
- final public release verification:
  `make check-public-release-final-package`;
- daily automation report complete:
  `type_theory_atlas_daily_automation_report_complete_holds`;
- automation done dashboard certificate:
  `type_theory_atlas_automation_done_dashboard_certificate_holds`;
- automation done:
  `type_theory_atlas_automation_done_holds`;
- final public theorem:
  `type_theory_atlas_final_public_theorem_holds`;
- public final certificate:
  `type_theory_atlas_public_final_certificate_holds`;
- public delivery certificate:
  `type_theory_atlas_public_delivery_certificate_holds`;
- public summary certificate:
  `type_theory_atlas_public_summary_certificate_holds`;
- public theorem:
  `type_theory_atlas_public_theorem_holds`;
- public route certificate:
  `type_theory_atlas_public_route_certificate_holds`;
- public Atlas entry:
  `type_theory_atlas_public_entry_holds`;
- paper-ready automation complete certificate:
  `type_theory_atlas_paper_ready_automation_complete_certificate_holds`;
- paper-ready automation archive certificate:
  `type_theory_atlas_paper_ready_automation_archive_certificate_holds`;
- paper-ready project cover certificate:
  `type_theory_atlas_paper_ready_project_cover_certificate_holds`;
- paper-ready delivery certificate:
  `type_theory_atlas_paper_ready_delivery_certificate_holds`;
- paper-ready final report certificate:
  `type_theory_atlas_paper_ready_final_report_certificate_holds`;
- paper-ready abstract final certificate:
  `type_theory_atlas_paper_ready_abstract_final_certificate_holds`;
- paper-ready four-sentence index:
  `type_theory_atlas_paper_ready_four_sentence_index_holds`;
- paper-ready abstract certificate:
  `type_theory_atlas_paper_ready_abstract_certificate_holds`;
- paper-ready claim index:
  `type_theory_atlas_paper_ready_claim_index_holds`;
- paper-ready completion:
  `type_theory_atlas_paper_ready_completion_certificate_holds`;
- daily final dashboard completion:
  `type_theory_atlas_daily_final_dashboard_completion_certificate_holds`;
- daily final dashboard:
  `type_theory_atlas_daily_final_dashboard_certificate_holds`;
- daily automation summary:
  `type_theory_atlas_daily_automation_summary_certificate_holds`;
- daily final report index:
  `type_theory_atlas_daily_final_report_index_holds`;
- daily report conclusion:
  `type_theory_atlas_daily_report_conclusion_holds`;
- daily release certificate:
  `type_theory_atlas_daily_release_certificate_holds`;
- daily automation facade: `type_theory_atlas_daily_report_facade_holds`;
- foundational daily-complete certificate: `type_theory_atlas_daily_complete`;
- artifact completion: `type_theory_atlas_complete`;
- paper-facing statement: `type_theory_atlas_paper_statement_holds`;
- current build status: see `Build Status Summary`.

## Contents

- [Current Stage](#current-stage)
- [Entry Consistency Checklist](#entry-consistency-checklist)
- [Verified Metatheory](#verified-metatheory)
- [Quick Stage Index](#quick-stage-index)
- [Daily Complete Entry Point](#daily-complete-entry-point)
- [Daily Stage Route Index](#daily-stage-route-index)
- [Daily Phase Route Consistency](#daily-phase-route-consistency)
- [Daily Final Route Certificate](#daily-final-route-certificate)
- [Daily Automation Final Entry Index](#daily-automation-final-entry-index)
- [Daily Deliverable Completion Certificate](#daily-deliverable-completion-certificate)
- [Daily Report Facade](#daily-report-facade)
- [Daily Release Certificate](#daily-release-certificate)
- [Daily Report Conclusion](#daily-report-conclusion)
- [Daily Final Report Index](#daily-final-report-index)
- [Homepage Summary](#homepage-summary)
- [GitHub Homepage Snippet](#github-homepage-snippet)
- [Public Release Citation](#public-release-citation)
- [Build Status Summary](#build-status-summary)
- [Build](#build)

## Entry Consistency Checklist

The README-facing entry names are kept aligned with
`theories/Atlas/Metatheory.v` as follows:

- Current top-level entries:
  `type_theory_atlas_public_release_paper_route_holds`,
  `type_theory_atlas_public_release_paper_route_certificate_holds`,
  `type_theory_atlas_public_release_complete_holds`,
  `type_theory_atlas_public_release_complete_certificate_holds`,
  `type_theory_atlas_automation_done_dashboard_certificate_holds`,
  `type_theory_atlas_automation_done_holds`,
  `type_theory_atlas_final_public_theorem_holds`,
  `type_theory_atlas_public_final_certificate_holds`,
  `type_theory_atlas_public_delivery_certificate_holds`,
  `type_theory_atlas_public_summary_certificate_holds`,
  `type_theory_atlas_public_theorem_holds`,
  `type_theory_atlas_public_route_certificate_holds`,
  `type_theory_atlas_public_entry_holds`,
  `type_theory_atlas_paper_ready_automation_complete_certificate_holds`,
  `type_theory_atlas_paper_ready_automation_archive_certificate_holds`,
  `type_theory_atlas_paper_ready_project_cover_certificate_holds`,
  `type_theory_atlas_paper_ready_delivery_certificate_holds`,
  `type_theory_atlas_paper_ready_final_report_certificate_holds`,
  `type_theory_atlas_paper_ready_abstract_final_certificate_holds`,
  `type_theory_atlas_paper_ready_four_sentence_index_holds`,
  `type_theory_atlas_paper_ready_abstract_certificate_holds`,
  `type_theory_atlas_paper_ready_claim_index_holds`,
  `type_theory_atlas_paper_ready_completion_certificate_holds`,
  `type_theory_atlas_daily_final_dashboard_completion_certificate_holds`,
  `type_theory_atlas_daily_final_dashboard_certificate_holds`,
  `type_theory_atlas_daily_automation_summary_certificate_holds`,
  `type_theory_atlas_daily_final_report_index_holds`,
  `type_theory_atlas_daily_report_conclusion_holds`,
  `type_theory_atlas_daily_release_certificate_holds`,
  `type_theory_atlas_daily_report_facade_holds`,
  `type_theory_atlas_daily_complete`,
  `type_theory_atlas_complete`, and
  `type_theory_atlas_paper_statement_holds`.
- Daily automation facade entry:
  `type_theory_atlas_daily_report_facade_holds`.
- Foundational daily-complete entry:
  `type_theory_atlas_daily_complete`.
- Artifact completion entry:
  `type_theory_atlas_complete`.
- Paper-facing statement:
  `type_theory_atlas_paper_statement_holds`.
- Unified syntax route:
  `type_theory_atlas_daily_completion_gives_unified_syntax`.
- MLTT route:
  `type_theory_atlas_daily_completion_gives_mltt`.
- UTT route:
  `type_theory_atlas_daily_completion_gives_utt`.
- TDTT route:
  `type_theory_atlas_daily_completion_gives_tdtt`.
- System translation route:
  `atlas_system_embedding_regularities_hold`,
  `atlas_translation_reliability_summary_holds`, and
  `type_theory_atlas_daily_completion_gives_translation`.
- Metatheory route:
  `type_theory_atlas_daily_completion_gives_metatheory`.
- Daily complete route projections:
  `type_theory_atlas_daily_complete_gives_unified_syntax`,
  `type_theory_atlas_daily_complete_gives_mltt`,
  `type_theory_atlas_daily_complete_gives_utt`,
  `type_theory_atlas_daily_complete_gives_tdtt_typing`,
  `type_theory_atlas_daily_complete_gives_tdtt`,
  `type_theory_atlas_daily_complete_gives_system_embeddings`, and
  `type_theory_atlas_daily_complete_gives_translation`.
- Daily stage route index:
  `type_theory_atlas_daily_stage_route_index_holds` and
  `type_theory_atlas_daily_complete_gives_stage_route_index`.
- Daily phase route consistency:
  `type_theory_atlas_daily_stage_route_index_from_phase_order`,
  `type_theory_atlas_daily_phase_route_consistency_holds`, and
  `type_theory_atlas_daily_complete_gives_phase_route_consistency`.
- Daily phase route projections:
  `type_theory_atlas_daily_phase_route_gives_stage_route_index`,
  `type_theory_atlas_daily_phase_route_gives_phase_order`,
  `type_theory_atlas_daily_phase_route_gives_unified_syntax`,
  `type_theory_atlas_daily_phase_route_gives_mltt`,
  `type_theory_atlas_daily_phase_route_gives_utt`,
  `type_theory_atlas_daily_phase_route_gives_tdtt_typing`,
  `type_theory_atlas_daily_phase_route_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_phase_route_gives_system_embeddings`,
  `type_theory_atlas_daily_phase_route_gives_translation`,
  `type_theory_atlas_daily_phase_route_gives_metatheory`, and
  `type_theory_atlas_daily_phase_route_gives_artifact_index`.
- Daily final route certificate:
  `type_theory_atlas_daily_final_route_certificate`,
  `type_theory_atlas_daily_final_route_certificate_holds`, and
  `type_theory_atlas_daily_complete_gives_final_route_certificate`.
- Daily final route projections:
  `type_theory_atlas_daily_final_route_gives_report`,
  `type_theory_atlas_daily_final_route_gives_daily_complete`,
  `type_theory_atlas_daily_final_route_gives_phase_consistency`,
  `type_theory_atlas_daily_final_route_gives_stage_route_index`,
  `type_theory_atlas_daily_final_route_gives_phase_order`,
  `type_theory_atlas_daily_final_route_gives_unified_syntax`,
  `type_theory_atlas_daily_final_route_gives_mltt`,
  `type_theory_atlas_daily_final_route_gives_utt`,
  `type_theory_atlas_daily_final_route_gives_tdtt_typing`,
  `type_theory_atlas_daily_final_route_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_final_route_gives_system_embeddings`,
  `type_theory_atlas_daily_final_route_gives_translation`,
  `type_theory_atlas_daily_final_route_gives_metatheory`, and
  `type_theory_atlas_daily_final_route_gives_artifact_index`.
- Daily automation final entry index:
  `type_theory_atlas_daily_automation_final_entry_index`,
  `type_theory_atlas_daily_automation_final_entry_index_holds`, and
  `type_theory_atlas_daily_complete_gives_automation_final_entry_index`.
- Daily automation final entry projections:
  `type_theory_atlas_daily_final_entry_gives_daily_complete`,
  `type_theory_atlas_daily_final_entry_gives_complete_entry`,
  `type_theory_atlas_daily_final_entry_gives_final_route`,
  `type_theory_atlas_daily_final_entry_gives_report`,
  `type_theory_atlas_daily_final_entry_gives_phase_consistency`,
  `type_theory_atlas_daily_final_entry_gives_stage_route_index`,
  `type_theory_atlas_daily_final_entry_gives_phase_order`,
  `type_theory_atlas_daily_final_entry_gives_unified_syntax`,
  `type_theory_atlas_daily_final_entry_gives_mltt`,
  `type_theory_atlas_daily_final_entry_gives_utt`,
  `type_theory_atlas_daily_final_entry_gives_tdtt_typing`,
  `type_theory_atlas_daily_final_entry_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_final_entry_gives_system_embeddings`,
  `type_theory_atlas_daily_final_entry_gives_translation`,
  `type_theory_atlas_daily_final_entry_gives_metatheory`, and
  `type_theory_atlas_daily_final_entry_gives_artifact_index`.
- Daily deliverable completion certificate:
  `type_theory_atlas_daily_deliverable_completion_certificate`,
  `type_theory_atlas_daily_deliverable_completion_certificate_holds`, and
  `type_theory_atlas_daily_complete_gives_deliverable_completion`.
- Daily deliverable completion projections:
  `type_theory_atlas_daily_deliverable_gives_final_entry_index`,
  `type_theory_atlas_daily_deliverable_gives_daily_complete`,
  `type_theory_atlas_daily_deliverable_gives_complete_entry`,
  `type_theory_atlas_daily_deliverable_gives_final_route`,
  `type_theory_atlas_daily_deliverable_gives_report`,
  `type_theory_atlas_daily_deliverable_gives_phase_consistency`,
  `type_theory_atlas_daily_deliverable_gives_stage_route_index`,
  `type_theory_atlas_daily_deliverable_gives_phase_order`,
  `type_theory_atlas_daily_deliverable_gives_release_summary`,
  `type_theory_atlas_daily_deliverable_gives_project_status`,
  `type_theory_atlas_daily_deliverable_gives_artifact_index`,
  `type_theory_atlas_daily_deliverable_gives_unified_syntax`,
  `type_theory_atlas_daily_deliverable_gives_mltt`,
  `type_theory_atlas_daily_deliverable_gives_utt`,
  `type_theory_atlas_daily_deliverable_gives_tdtt_typing`,
  `type_theory_atlas_daily_deliverable_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_deliverable_gives_system_embeddings`,
  `type_theory_atlas_daily_deliverable_gives_translation`, and
  `type_theory_atlas_daily_deliverable_gives_metatheory`.
- Daily-complete deliverable projections:
  `type_theory_atlas_daily_complete_gives_deliverable_final_entry_index`,
  `type_theory_atlas_daily_complete_gives_deliverable_complete_entry`,
  `type_theory_atlas_daily_complete_gives_deliverable_final_route`,
  `type_theory_atlas_daily_complete_gives_deliverable_report`,
  `type_theory_atlas_daily_complete_gives_deliverable_phase_consistency`,
  `type_theory_atlas_daily_complete_gives_deliverable_stage_route_index`,
  `type_theory_atlas_daily_complete_gives_deliverable_phase_order`,
  `type_theory_atlas_daily_complete_gives_deliverable_release_summary`,
  `type_theory_atlas_daily_complete_gives_deliverable_project_status`,
  `type_theory_atlas_daily_complete_gives_deliverable_artifact_index`,
  `type_theory_atlas_daily_complete_gives_deliverable_unified_syntax`,
  `type_theory_atlas_daily_complete_gives_deliverable_mltt`,
  `type_theory_atlas_daily_complete_gives_deliverable_utt`,
  `type_theory_atlas_daily_complete_gives_deliverable_tdtt_typing`,
  `type_theory_atlas_daily_complete_gives_deliverable_tdtt_dashboard`,
  `type_theory_atlas_daily_complete_gives_deliverable_system_embeddings`,
  `type_theory_atlas_daily_complete_gives_deliverable_translation`, and
  `type_theory_atlas_daily_complete_gives_deliverable_metatheory`.
- Daily report facade:
  `type_theory_atlas_daily_report_facade`,
  `type_theory_atlas_daily_report_facade_holds`, and
  `type_theory_atlas_daily_complete_gives_report_facade`.
- Daily report facade projections:
  `type_theory_atlas_daily_report_facade_gives_entry_point`,
  `type_theory_atlas_daily_report_facade_gives_deliverable_completion`,
  `type_theory_atlas_daily_report_facade_gives_final_entry_index`,
  `type_theory_atlas_daily_report_facade_gives_complete_entry`,
  `type_theory_atlas_daily_report_facade_gives_final_route`,
  `type_theory_atlas_daily_report_facade_gives_report`,
  `type_theory_atlas_daily_report_facade_gives_phase_consistency`,
  `type_theory_atlas_daily_report_facade_gives_stage_route_index`,
  `type_theory_atlas_daily_report_facade_gives_phase_order`,
  `type_theory_atlas_daily_report_facade_gives_release_summary`,
  `type_theory_atlas_daily_report_facade_gives_project_status`,
  `type_theory_atlas_daily_report_facade_gives_artifact_index`,
  `type_theory_atlas_daily_report_facade_gives_unified_syntax`,
  `type_theory_atlas_daily_report_facade_gives_mltt`,
  `type_theory_atlas_daily_report_facade_gives_utt`,
  `type_theory_atlas_daily_report_facade_gives_tdtt_typing`,
  `type_theory_atlas_daily_report_facade_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_report_facade_gives_system_embeddings`,
  `type_theory_atlas_daily_report_facade_gives_translation`, and
  `type_theory_atlas_daily_report_facade_gives_metatheory`.
- Daily release certificate:
  `type_theory_atlas_daily_release_certificate`,
  `type_theory_atlas_daily_release_certificate_holds`, and
  `type_theory_atlas_daily_report_facade_gives_release_certificate`.
- Daily release certificate projections:
  `type_theory_atlas_daily_release_gives_report_facade`,
  `type_theory_atlas_daily_release_gives_stage_route_index`,
  `type_theory_atlas_daily_release_gives_phase_order`,
  `type_theory_atlas_daily_release_gives_final_delivery_index`,
  `type_theory_atlas_daily_release_gives_paper_claim_index`,
  `type_theory_atlas_daily_release_gives_paper_statement`, and
  `type_theory_atlas_daily_release_gives_main_theorem`.
- Daily release stage projections:
  `type_theory_atlas_daily_release_gives_unified_syntax`,
  `type_theory_atlas_daily_release_gives_mltt`,
  `type_theory_atlas_daily_release_gives_utt`,
  `type_theory_atlas_daily_release_gives_tdtt_typing`,
  `type_theory_atlas_daily_release_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_release_gives_system_embeddings`,
  `type_theory_atlas_daily_release_gives_translation`, and
  `type_theory_atlas_daily_release_gives_metatheory`.
- Daily release stage consistency:
  `type_theory_atlas_daily_release_stage_consistency`,
  `type_theory_atlas_daily_release_stage_consistency_holds`,
  `type_theory_atlas_daily_release_gives_stage_consistency`,
  `type_theory_atlas_daily_release_stage_consistency_gives_release`,
  `type_theory_atlas_daily_release_stage_consistency_gives_stage_route`,
  `type_theory_atlas_daily_release_stage_consistency_gives_phase_built_route`,
  and `type_theory_atlas_daily_release_stage_consistency_gives_phase_order`.
- Daily release stage consistency projections:
  `type_theory_atlas_daily_release_stage_consistency_gives_unified_syntax`,
  `type_theory_atlas_daily_release_stage_consistency_gives_mltt`,
  `type_theory_atlas_daily_release_stage_consistency_gives_utt`,
  `type_theory_atlas_daily_release_stage_consistency_gives_tdtt_typing`,
  `type_theory_atlas_daily_release_stage_consistency_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_release_stage_consistency_gives_system_embeddings`,
  `type_theory_atlas_daily_release_stage_consistency_gives_translation`, and
  `type_theory_atlas_daily_release_stage_consistency_gives_metatheory`.
- Daily report conclusion:
  `type_theory_atlas_daily_report_conclusion`,
  `type_theory_atlas_daily_report_conclusion_holds`, and
  `type_theory_atlas_daily_release_gives_report_conclusion`.
- Daily report conclusion projections:
  `type_theory_atlas_daily_report_conclusion_gives_release_certificate`,
  `type_theory_atlas_daily_report_conclusion_gives_stage_consistency`,
  `type_theory_atlas_daily_report_conclusion_gives_unified_syntax`,
  `type_theory_atlas_daily_report_conclusion_gives_mltt`,
  `type_theory_atlas_daily_report_conclusion_gives_utt`,
  `type_theory_atlas_daily_report_conclusion_gives_tdtt_typing`,
  `type_theory_atlas_daily_report_conclusion_gives_tdtt_dashboard`,
  `type_theory_atlas_daily_report_conclusion_gives_system_embeddings`,
  `type_theory_atlas_daily_report_conclusion_gives_translation`,
  `type_theory_atlas_daily_report_conclusion_gives_metatheory`, and
  `type_theory_atlas_daily_report_conclusion_gives_paper_statement`.
- Daily conclusion stage-order summary:
  `type_theory_atlas_daily_conclusion_stage_order_summary`,
  `type_theory_atlas_daily_conclusion_stage_order_summary_holds`, and
  `type_theory_atlas_daily_report_conclusion_gives_stage_order_summary`.
- Daily conclusion stage-order projections:
  `type_theory_atlas_daily_conclusion_stage_order_gives_conclusion`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage2_mltt`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage3_utt`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage5_translation`,
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_conclusion_stage_order_gives_stage6_paper_statement`.
- Daily final report index:
  `type_theory_atlas_daily_final_report_index`,
  `type_theory_atlas_daily_final_report_index_holds`, and
  `type_theory_atlas_daily_report_conclusion_gives_final_report_index`.
- Daily final report index projections:
  `type_theory_atlas_daily_final_report_gives_conclusion`,
  `type_theory_atlas_daily_final_report_gives_stage_order_summary`,
  `type_theory_atlas_daily_final_report_gives_release_certificate`,
  `type_theory_atlas_daily_final_report_gives_stage_consistency`,
  `type_theory_atlas_daily_final_report_gives_metatheory`, and
  `type_theory_atlas_daily_final_report_gives_paper_statement`.
- Daily final report stage projections:
  `type_theory_atlas_daily_final_report_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_final_report_gives_stage2_mltt`,
  `type_theory_atlas_daily_final_report_gives_stage3_utt`,
  `type_theory_atlas_daily_final_report_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_final_report_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_final_report_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_final_report_gives_stage5_translation`,
  `type_theory_atlas_daily_final_report_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_final_report_gives_stage6_paper_statement`.
- Daily final stage-sync certificate:
  `type_theory_atlas_daily_final_stage_sync_certificate`,
  `type_theory_atlas_daily_final_stage_sync_certificate_holds`, and
  `type_theory_atlas_daily_final_report_gives_stage_sync_certificate`.
- Daily automation summary certificate:
  `type_theory_atlas_daily_automation_summary_certificate`,
  `type_theory_atlas_daily_automation_summary_certificate_holds`, and
  `type_theory_atlas_daily_final_report_gives_automation_summary_certificate`.
- Daily automation summary projections:
  `type_theory_atlas_daily_automation_summary_gives_final_report`,
  `type_theory_atlas_daily_automation_summary_gives_stage_sync`,
  `type_theory_atlas_daily_automation_summary_gives_conclusion`,
  `type_theory_atlas_daily_automation_summary_gives_release_certificate`,
  `type_theory_atlas_daily_automation_summary_gives_facade`,
  `type_theory_atlas_daily_automation_summary_gives_daily_complete`,
  `type_theory_atlas_daily_automation_summary_gives_artifact_complete`,
  `type_theory_atlas_daily_automation_summary_gives_release_summary`,
  `type_theory_atlas_daily_automation_summary_gives_project_status`,
  `type_theory_atlas_daily_automation_summary_gives_metatheory`, and
  `type_theory_atlas_daily_automation_summary_gives_paper_statement`.
- Daily automation summary stage projections:
  `type_theory_atlas_daily_automation_summary_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_automation_summary_gives_stage2_mltt`,
  `type_theory_atlas_daily_automation_summary_gives_stage3_utt`,
  `type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_automation_summary_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_automation_summary_gives_stage5_translation`,
  `type_theory_atlas_daily_automation_summary_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_automation_summary_gives_stage6_paper_statement`.
- Daily automation stage-route certificate:
  `type_theory_atlas_daily_automation_stage_route_certificate`,
  `type_theory_atlas_daily_automation_stage_route_certificate_holds`, and
  `type_theory_atlas_daily_automation_summary_gives_stage_route_certificate`.
- Daily automation stage-route projections:
  `type_theory_atlas_daily_automation_stage_route_gives_summary`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage_sync`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage2_mltt`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage3_utt`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage5_translation`,
  `type_theory_atlas_daily_automation_stage_route_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_automation_stage_route_gives_stage6_paper_statement`.
- Daily final dashboard certificate:
  `type_theory_atlas_daily_final_dashboard_certificate`,
  `type_theory_atlas_daily_final_dashboard_certificate_holds`, and
  `type_theory_atlas_daily_automation_summary_gives_final_dashboard`.
- Daily final dashboard projections:
  `type_theory_atlas_daily_final_dashboard_gives_automation_summary`,
  `type_theory_atlas_daily_final_dashboard_gives_stage_route`,
  `type_theory_atlas_daily_final_dashboard_gives_final_report`,
  `type_theory_atlas_daily_final_dashboard_gives_stage_sync`,
  `type_theory_atlas_daily_final_dashboard_gives_release_summary`,
  `type_theory_atlas_daily_final_dashboard_gives_project_status`,
  `type_theory_atlas_daily_final_dashboard_gives_metatheory`, and
  `type_theory_atlas_daily_final_dashboard_gives_paper_statement`.
- Daily final dashboard stage projections:
  `type_theory_atlas_daily_final_dashboard_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_final_dashboard_gives_stage2_mltt`,
  `type_theory_atlas_daily_final_dashboard_gives_stage3_utt`,
  `type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_final_dashboard_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_final_dashboard_gives_stage5_translation`,
  `type_theory_atlas_daily_final_dashboard_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_final_dashboard_gives_stage6_paper_statement`.
- Daily final dashboard stage-route certificate:
  `type_theory_atlas_daily_final_dashboard_stage_route_certificate`,
  `type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds`, and
  `type_theory_atlas_daily_final_dashboard_gives_stage_route_certificate`.
- Daily final dashboard stage-route projections:
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_dashboard`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_route`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage2_mltt`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage3_utt`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_translation`,
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_paper_statement`.
- Daily final dashboard completion certificate:
  `type_theory_atlas_daily_final_dashboard_completion_certificate`,
  `type_theory_atlas_daily_final_dashboard_completion_certificate_holds`, and
  `type_theory_atlas_daily_final_dashboard_gives_completion_certificate`.
- Daily final dashboard completion projections:
  `type_theory_atlas_daily_final_dashboard_completion_gives_dashboard`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage_route`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_automation_summary`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_final_report`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_release_summary`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_project_status`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_metatheory`, and
  `type_theory_atlas_daily_final_dashboard_completion_gives_paper_statement`.
- Daily final dashboard completion stage projections:
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage2_mltt`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage3_utt`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage5_translation`,
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_final_dashboard_completion_gives_stage6_paper_statement`.
- Paper-ready completion certificate:
  `type_theory_atlas_paper_ready_completion_certificate`,
  `type_theory_atlas_paper_ready_completion_certificate_holds`, and
  `type_theory_atlas_daily_final_dashboard_completion_gives_paper_ready_certificate`.
- Paper-ready completion projections:
  `type_theory_atlas_paper_ready_completion_gives_completion_handle`,
  `type_theory_atlas_paper_ready_completion_gives_dashboard`,
  `type_theory_atlas_paper_ready_completion_gives_stage_route`,
  `type_theory_atlas_paper_ready_completion_gives_unified_syntax`,
  `type_theory_atlas_paper_ready_completion_gives_mltt`,
  `type_theory_atlas_paper_ready_completion_gives_utt`,
  `type_theory_atlas_paper_ready_completion_gives_tdtt_typing`,
  `type_theory_atlas_paper_ready_completion_gives_tdtt_dashboard`,
  `type_theory_atlas_paper_ready_completion_gives_system_embeddings`,
  `type_theory_atlas_paper_ready_completion_gives_translation`,
  `type_theory_atlas_paper_ready_completion_gives_metatheory`, and
  `type_theory_atlas_paper_ready_completion_gives_paper_statement`.
- Paper-ready claim index:
  `type_theory_atlas_paper_ready_claim_index`,
  `type_theory_atlas_paper_ready_claim_index_holds`, and
  `type_theory_atlas_paper_ready_completion_gives_claim_index`.
- Paper-ready claim projections:
  `type_theory_atlas_paper_ready_claim_gives_completion`,
  `type_theory_atlas_paper_ready_claim_gives_claim_index`,
  `type_theory_atlas_paper_ready_claim_gives_statement`,
  `type_theory_atlas_paper_ready_claim_gives_final_paper_theorem`,
  `type_theory_atlas_paper_ready_claim_gives_contribution_summary`,
  `type_theory_atlas_paper_ready_claim_gives_system_comparison`,
  `type_theory_atlas_paper_ready_claim_gives_translation`,
  `type_theory_atlas_paper_ready_claim_gives_tdtt`, and
  `type_theory_atlas_paper_ready_claim_gives_metatheory`.
- Paper-ready abstract certificate:
  `type_theory_atlas_paper_ready_abstract_certificate`,
  `type_theory_atlas_paper_ready_abstract_certificate_holds`, and
  `type_theory_atlas_paper_ready_claim_gives_abstract_certificate`.
- Paper-ready abstract projections:
  `type_theory_atlas_paper_ready_abstract_gives_claim_index`,
  `type_theory_atlas_paper_ready_abstract_gives_completion`,
  `type_theory_atlas_paper_ready_abstract_gives_unified_framework`,
  `type_theory_atlas_paper_ready_abstract_gives_mltt`,
  `type_theory_atlas_paper_ready_abstract_gives_utt`,
  `type_theory_atlas_paper_ready_abstract_gives_tdtt_typing`,
  `type_theory_atlas_paper_ready_abstract_gives_tdtt_dashboard`,
  `type_theory_atlas_paper_ready_abstract_gives_translation`,
  `type_theory_atlas_paper_ready_abstract_gives_metatheory`, and
  `type_theory_atlas_paper_ready_abstract_gives_paper_statement`.
- Paper-ready four-sentence index:
  `type_theory_atlas_paper_ready_four_sentence_index`,
  `type_theory_atlas_paper_ready_four_sentence_index_holds`, and
  `type_theory_atlas_paper_ready_abstract_gives_four_sentence_index`.
- Paper-ready four-sentence projections:
  `type_theory_atlas_paper_ready_four_sentence_gives_unified_framework`,
  `type_theory_atlas_paper_ready_four_sentence_gives_three_systems`,
  `type_theory_atlas_paper_ready_four_sentence_gives_translations`,
  `type_theory_atlas_paper_ready_four_sentence_gives_metatheory`, and
  `type_theory_atlas_paper_ready_four_sentence_gives_paper_statement`.
- Paper-ready abstract sentence projections:
  `type_theory_atlas_paper_ready_abstract_sentence_1_unified_framework`,
  `type_theory_atlas_paper_ready_abstract_sentence_2_three_systems`,
  `type_theory_atlas_paper_ready_abstract_sentence_3_translations`, and
  `type_theory_atlas_paper_ready_abstract_sentence_4_metatheory`.
- Paper-ready abstract final certificate:
  `type_theory_atlas_paper_ready_abstract_final_certificate`,
  `type_theory_atlas_paper_ready_abstract_final_certificate_holds`, and
  `type_theory_atlas_paper_ready_four_sentence_gives_abstract_final_certificate`.
- Paper-ready abstract final projections:
  `type_theory_atlas_paper_ready_abstract_final_gives_four_sentence_index`,
  `type_theory_atlas_paper_ready_abstract_final_gives_sentence_1`,
  `type_theory_atlas_paper_ready_abstract_final_gives_sentence_2`,
  `type_theory_atlas_paper_ready_abstract_final_gives_sentence_3`,
  `type_theory_atlas_paper_ready_abstract_final_gives_sentence_4`, and
  `type_theory_atlas_paper_ready_abstract_final_gives_paper_statement`.
- Paper-ready final report certificate:
  `type_theory_atlas_paper_ready_final_report_certificate`,
  `type_theory_atlas_paper_ready_final_report_certificate_holds`, and
  `type_theory_atlas_paper_ready_abstract_final_gives_final_report_certificate`.
- Paper-ready final report projections:
  `type_theory_atlas_paper_ready_final_report_gives_abstract_final`,
  `type_theory_atlas_paper_ready_final_report_gives_daily_completion`,
  `type_theory_atlas_paper_ready_final_report_gives_daily_report`,
  `type_theory_atlas_paper_ready_final_report_gives_dashboard`,
  `type_theory_atlas_paper_ready_final_report_gives_stage_route`,
  `type_theory_atlas_paper_ready_final_report_gives_four_sentence_index`,
  `type_theory_atlas_paper_ready_final_report_gives_metatheory`, and
  `type_theory_atlas_paper_ready_final_report_gives_paper_statement`.
- Paper-ready delivery certificate:
  `type_theory_atlas_paper_ready_delivery_certificate`,
  `type_theory_atlas_paper_ready_delivery_certificate_holds`, and
  `type_theory_atlas_paper_ready_final_report_gives_delivery_certificate`.
- Paper-ready delivery projections:
  `type_theory_atlas_paper_ready_delivery_gives_final_report`,
  `type_theory_atlas_paper_ready_delivery_gives_daily_completion`,
  `type_theory_atlas_paper_ready_delivery_gives_release_summary`,
  `type_theory_atlas_paper_ready_delivery_gives_project_status`,
  `type_theory_atlas_paper_ready_delivery_gives_dashboard`,
  `type_theory_atlas_paper_ready_delivery_gives_abstract_final`,
  `type_theory_atlas_paper_ready_delivery_gives_four_sentence_index`,
  `type_theory_atlas_paper_ready_delivery_gives_metatheory`, and
  `type_theory_atlas_paper_ready_delivery_gives_paper_statement`.
- Paper-ready project cover certificate:
  `type_theory_atlas_paper_ready_project_cover_certificate`,
  `type_theory_atlas_paper_ready_project_cover_certificate_holds`, and
  `type_theory_atlas_paper_ready_delivery_gives_project_cover_certificate`.
- Paper-ready project cover projections:
  `type_theory_atlas_paper_ready_project_cover_gives_delivery`,
  `type_theory_atlas_paper_ready_project_cover_gives_paper_statement`,
  `type_theory_atlas_paper_ready_project_cover_gives_core_contribution`,
  `type_theory_atlas_paper_ready_project_cover_gives_abstract_final`,
  `type_theory_atlas_paper_ready_project_cover_gives_four_sentence_index`,
  `type_theory_atlas_paper_ready_project_cover_gives_release_summary`,
  `type_theory_atlas_paper_ready_project_cover_gives_project_status`,
  `type_theory_atlas_paper_ready_project_cover_gives_daily_completion`,
  `type_theory_atlas_paper_ready_project_cover_gives_validation_dashboard`, and
  `type_theory_atlas_paper_ready_project_cover_gives_metatheory`.
- Paper-ready automation archive certificate:
  `type_theory_atlas_paper_ready_automation_archive_certificate`,
  `type_theory_atlas_paper_ready_automation_archive_certificate_holds`, and
  `type_theory_atlas_paper_ready_project_cover_gives_automation_archive_certificate`.
- Paper-ready automation archive projections:
  `type_theory_atlas_paper_ready_archive_gives_project_cover`,
  `type_theory_atlas_paper_ready_archive_gives_delivery`,
  `type_theory_atlas_paper_ready_archive_gives_daily_completion`,
  `type_theory_atlas_paper_ready_archive_gives_automation_summary`,
  `type_theory_atlas_paper_ready_archive_gives_final_dashboard`,
  `type_theory_atlas_paper_ready_archive_gives_release_summary`,
  `type_theory_atlas_paper_ready_archive_gives_project_status`,
  `type_theory_atlas_paper_ready_archive_gives_stage_route`,
  `type_theory_atlas_paper_ready_archive_gives_metatheory`, and
  `type_theory_atlas_paper_ready_archive_gives_paper_statement`.
- Paper-ready automation complete certificate:
  `type_theory_atlas_paper_ready_automation_complete_certificate`,
  `type_theory_atlas_paper_ready_automation_complete_certificate_holds`, and
  `type_theory_atlas_paper_ready_archive_gives_automation_complete_certificate`.
- Paper-ready automation complete projections:
  `type_theory_atlas_paper_ready_complete_gives_archive`,
  `type_theory_atlas_paper_ready_complete_gives_project_cover`,
  `type_theory_atlas_paper_ready_complete_gives_delivery`,
  `type_theory_atlas_paper_ready_complete_gives_four_sentence_index`,
  `type_theory_atlas_paper_ready_complete_gives_daily_completion`,
  `type_theory_atlas_paper_ready_complete_gives_automation_summary`,
  `type_theory_atlas_paper_ready_complete_gives_final_dashboard`,
  `type_theory_atlas_paper_ready_complete_gives_stage_route`,
  `type_theory_atlas_paper_ready_complete_gives_metatheory`, and
  `type_theory_atlas_paper_ready_complete_gives_paper_statement`.
- Public Atlas entry:
  `type_theory_atlas_public_entry`,
  `type_theory_atlas_public_entry_holds`,
  `type_theory_atlas_public_entry_gives_paper_ready_complete`,
  `type_theory_atlas_public_entry_gives_daily_completion`,
  `type_theory_atlas_public_entry_gives_automation_summary`,
  `type_theory_atlas_public_entry_gives_final_dashboard`,
  `type_theory_atlas_public_entry_gives_stage_route`,
  `type_theory_atlas_public_entry_gives_unified_syntax`,
  `type_theory_atlas_public_entry_gives_mltt`,
  `type_theory_atlas_public_entry_gives_utt`,
  `type_theory_atlas_public_entry_gives_tdtt_typing`,
  `type_theory_atlas_public_entry_gives_tdtt_dashboard`,
  `type_theory_atlas_public_entry_gives_system_embeddings`,
  `type_theory_atlas_public_entry_gives_translation_reliability`,
  `type_theory_atlas_public_entry_gives_main_theorem`, and
  `type_theory_atlas_public_entry_gives_paper_statement`.
- Public route certificate:
  `type_theory_atlas_public_route_certificate`,
  `type_theory_atlas_public_route_certificate_holds`, and
  `type_theory_atlas_public_entry_gives_route_certificate`.
- Public route projections:
  `type_theory_atlas_public_route_gives_entry`,
  `type_theory_atlas_public_route_gives_unified_syntax`,
  `type_theory_atlas_public_route_gives_mltt`,
  `type_theory_atlas_public_route_gives_utt`,
  `type_theory_atlas_public_route_gives_tdtt_typing`,
  `type_theory_atlas_public_route_gives_tdtt_dashboard`,
  `type_theory_atlas_public_route_gives_system_embeddings`,
  `type_theory_atlas_public_route_gives_translation_reliability`,
  `type_theory_atlas_public_route_gives_main_theorem`, and
  `type_theory_atlas_public_route_gives_paper_statement`.
- Public theorem:
  `type_theory_atlas_public_theorem`,
  `type_theory_atlas_public_theorem_holds`,
  `type_theory_atlas_public_theorem_gives_route_certificate`,
  `type_theory_atlas_public_theorem_gives_unified_syntax`,
  `type_theory_atlas_public_theorem_gives_mltt`,
  `type_theory_atlas_public_theorem_gives_utt`,
  `type_theory_atlas_public_theorem_gives_tdtt_typing`,
  `type_theory_atlas_public_theorem_gives_tdtt_dashboard`,
  `type_theory_atlas_public_theorem_gives_system_embeddings`,
  `type_theory_atlas_public_theorem_gives_translation_reliability`,
  `type_theory_atlas_public_theorem_gives_main_theorem`, and
  `type_theory_atlas_public_theorem_gives_paper_statement`.
- Public summary certificate:
  `type_theory_atlas_public_summary_certificate`,
  `type_theory_atlas_public_summary_certificate_holds`,
  `type_theory_atlas_public_theorem_gives_summary_certificate`,
  `type_theory_atlas_public_summary_gives_public_theorem`,
  `type_theory_atlas_public_summary_gives_route_certificate`,
  `type_theory_atlas_public_summary_gives_unified_syntax`,
  `type_theory_atlas_public_summary_gives_mltt`,
  `type_theory_atlas_public_summary_gives_utt`,
  `type_theory_atlas_public_summary_gives_tdtt_typing`,
  `type_theory_atlas_public_summary_gives_tdtt_dashboard`,
  `type_theory_atlas_public_summary_gives_system_embeddings`,
  `type_theory_atlas_public_summary_gives_translation_reliability`,
  `type_theory_atlas_public_summary_gives_main_theorem`, and
  `type_theory_atlas_public_summary_gives_paper_statement`.
- Public delivery certificate:
  `type_theory_atlas_public_delivery_certificate`,
  `type_theory_atlas_public_delivery_certificate_holds`, and
  `type_theory_atlas_public_summary_gives_delivery_certificate`.
- Public delivery projections:
  `type_theory_atlas_public_delivery_gives_summary`,
  `type_theory_atlas_public_delivery_gives_public_theorem`,
  `type_theory_atlas_public_delivery_gives_route_certificate`,
  `type_theory_atlas_public_delivery_gives_unified_syntax`,
  `type_theory_atlas_public_delivery_gives_mltt`,
  `type_theory_atlas_public_delivery_gives_utt`,
  `type_theory_atlas_public_delivery_gives_tdtt_typing`,
  `type_theory_atlas_public_delivery_gives_tdtt_dashboard`,
  `type_theory_atlas_public_delivery_gives_system_embeddings`,
  `type_theory_atlas_public_delivery_gives_translation_reliability`,
  `type_theory_atlas_public_delivery_gives_main_theorem`, and
  `type_theory_atlas_public_delivery_gives_paper_statement`.
- Public final certificate:
  `type_theory_atlas_public_final_certificate`,
  `type_theory_atlas_public_final_certificate_holds`, and
  `type_theory_atlas_public_delivery_gives_final_certificate`.
- Public final projections:
  `type_theory_atlas_public_final_gives_delivery`,
  `type_theory_atlas_public_final_gives_summary`,
  `type_theory_atlas_public_final_gives_public_theorem`,
  `type_theory_atlas_public_final_gives_route_certificate`,
  `type_theory_atlas_public_final_gives_entry`,
  `type_theory_atlas_public_final_gives_unified_syntax`,
  `type_theory_atlas_public_final_gives_mltt`,
  `type_theory_atlas_public_final_gives_utt`,
  `type_theory_atlas_public_final_gives_tdtt_typing`,
  `type_theory_atlas_public_final_gives_tdtt_dashboard`,
  `type_theory_atlas_public_final_gives_system_embeddings`,
  `type_theory_atlas_public_final_gives_translation_reliability`,
  `type_theory_atlas_public_final_gives_main_theorem`, and
  `type_theory_atlas_public_final_gives_paper_statement`.
- Final public theorem:
  `type_theory_atlas_final_public_theorem`,
  `type_theory_atlas_final_public_theorem_holds`,
  `type_theory_atlas_final_public_theorem_gives_final_certificate`,
  `type_theory_atlas_final_public_theorem_gives_unified_syntax`,
  `type_theory_atlas_final_public_theorem_gives_mltt`,
  `type_theory_atlas_final_public_theorem_gives_utt`,
  `type_theory_atlas_final_public_theorem_gives_tdtt_typing`,
  `type_theory_atlas_final_public_theorem_gives_tdtt_dashboard`,
  `type_theory_atlas_final_public_theorem_gives_system_embeddings`,
  `type_theory_atlas_final_public_theorem_gives_translation_reliability`,
  `type_theory_atlas_final_public_theorem_gives_main_theorem`, and
  `type_theory_atlas_final_public_theorem_gives_paper_statement`.
- Automation done:
  `type_theory_atlas_automation_done`,
  `type_theory_atlas_automation_done_holds`,
  `type_theory_atlas_automation_done_gives_final_public_theorem`,
  `type_theory_atlas_automation_done_gives_unified_syntax`,
  `type_theory_atlas_automation_done_gives_mltt`,
  `type_theory_atlas_automation_done_gives_utt`,
  `type_theory_atlas_automation_done_gives_tdtt_typing`,
  `type_theory_atlas_automation_done_gives_tdtt_dashboard`,
  `type_theory_atlas_automation_done_gives_system_embeddings`,
  `type_theory_atlas_automation_done_gives_translation_reliability`,
  `type_theory_atlas_automation_done_gives_main_theorem`, and
  `type_theory_atlas_automation_done_gives_paper_statement`.
- Automation done dashboard certificate:
  `type_theory_atlas_automation_done_dashboard_certificate`,
  `type_theory_atlas_automation_done_dashboard_certificate_holds`, and
  `type_theory_atlas_automation_done_gives_dashboard_certificate`.
- Automation done dashboard projections:
  `type_theory_atlas_automation_dashboard_gives_done`,
  `type_theory_atlas_automation_dashboard_gives_final_public_theorem`,
  `type_theory_atlas_automation_dashboard_gives_unified_syntax`,
  `type_theory_atlas_automation_dashboard_gives_mltt`,
  `type_theory_atlas_automation_dashboard_gives_utt`,
  `type_theory_atlas_automation_dashboard_gives_tdtt_typing`,
  `type_theory_atlas_automation_dashboard_gives_tdtt_dashboard`,
  `type_theory_atlas_automation_dashboard_gives_system_embeddings`,
  `type_theory_atlas_automation_dashboard_gives_translation_reliability`,
  `type_theory_atlas_automation_dashboard_gives_main_theorem`, and
  `type_theory_atlas_automation_dashboard_gives_paper_statement`.
- Daily automation report complete:
  `type_theory_atlas_daily_automation_report_complete`,
  `type_theory_atlas_daily_automation_report_complete_holds`,
  `type_theory_atlas_daily_automation_report_complete_gives_dashboard`,
  `type_theory_atlas_daily_automation_report_complete_gives_done`,
  `type_theory_atlas_daily_automation_report_complete_gives_final_public_theorem`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage3_utt`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability`,
  `type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory`, and
  `type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement`.
- Public release manifest:
  `type_theory_atlas_public_release_manifest`,
  `type_theory_atlas_public_release_manifest_holds`,
  `type_theory_atlas_daily_automation_report_complete_gives_release_manifest`,
  `type_theory_atlas_public_release_manifest_gives_daily_report`,
  `type_theory_atlas_public_release_manifest_gives_dashboard`,
  `type_theory_atlas_public_release_manifest_gives_final_public_theorem`,
  `type_theory_atlas_public_release_manifest_gives_final_certificate`,
  `type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax`,
  `type_theory_atlas_public_release_manifest_gives_stage2_mltt`,
  `type_theory_atlas_public_release_manifest_gives_stage3_utt`,
  `type_theory_atlas_public_release_manifest_gives_stage4_tdtt_typing`,
  `type_theory_atlas_public_release_manifest_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_public_release_manifest_gives_stage5_system_embeddings`,
  `type_theory_atlas_public_release_manifest_gives_stage5_translation_reliability`,
  `type_theory_atlas_public_release_manifest_gives_stage6_metatheory`, and
  `type_theory_atlas_public_release_manifest_gives_paper_statement`.
- Public release complete entry and certificate:
  `type_theory_atlas_public_release_complete`,
  `type_theory_atlas_public_release_complete_holds`,
  `type_theory_atlas_public_release_complete_gives_certificate`,
  `type_theory_atlas_public_release_complete_certificate`,
  `type_theory_atlas_public_release_complete_certificate_holds`,
  `type_theory_atlas_public_release_manifest_gives_complete_certificate`,
  `type_theory_atlas_public_release_complete_gives_manifest`,
  `type_theory_atlas_public_release_complete_gives_daily_report`,
  `type_theory_atlas_public_release_complete_gives_dashboard`,
  `type_theory_atlas_public_release_complete_gives_final_public_theorem`,
  `type_theory_atlas_public_release_complete_gives_final_certificate`,
  `type_theory_atlas_public_release_complete_gives_stage1_unified_syntax`,
  `type_theory_atlas_public_release_complete_gives_stage2_mltt`,
  `type_theory_atlas_public_release_complete_gives_stage3_utt`,
  `type_theory_atlas_public_release_complete_gives_stage4_tdtt_typing`,
  `type_theory_atlas_public_release_complete_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_public_release_complete_gives_stage5_system_embeddings`,
  `type_theory_atlas_public_release_complete_gives_stage5_translation_reliability`,
  `type_theory_atlas_public_release_complete_gives_stage6_metatheory`, and
  `type_theory_atlas_public_release_complete_gives_paper_statement`.
- Public release complete entry projections:
  `type_theory_atlas_public_release_complete_entry_gives_stage1_unified_syntax`,
  `type_theory_atlas_public_release_complete_entry_gives_stage2_mltt`,
  `type_theory_atlas_public_release_complete_entry_gives_stage3_utt`,
  `type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_typing`,
  `type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_public_release_complete_entry_gives_stage5_system_embeddings`,
  `type_theory_atlas_public_release_complete_entry_gives_stage5_translation_reliability`,
  `type_theory_atlas_public_release_complete_entry_gives_stage6_metatheory`, and
  `type_theory_atlas_public_release_complete_entry_gives_paper_statement`.
- Public release paper route entry and certificate:
  `type_theory_atlas_public_release_paper_route`,
  `type_theory_atlas_public_release_paper_route_holds`,
  `type_theory_atlas_public_release_paper_route_gives_certificate`,
  `type_theory_atlas_public_release_paper_route_certificate`,
  `type_theory_atlas_public_release_paper_route_certificate_holds`,
  `type_theory_atlas_public_release_complete_gives_paper_route_certificate`,
  `type_theory_atlas_public_release_paper_route_gives_complete`,
  `type_theory_atlas_public_release_paper_route_gives_stage1_unified_syntax`,
  `type_theory_atlas_public_release_paper_route_gives_stage2_mltt`,
  `type_theory_atlas_public_release_paper_route_gives_stage3_utt`,
  `type_theory_atlas_public_release_paper_route_gives_stage4_tdtt_typing`,
  `type_theory_atlas_public_release_paper_route_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_public_release_paper_route_gives_stage5_system_embeddings`,
  `type_theory_atlas_public_release_paper_route_gives_stage5_translation_reliability`,
  `type_theory_atlas_public_release_paper_route_gives_stage6_metatheory`, and
  `type_theory_atlas_public_release_paper_route_gives_paper_statement`.
- Public release paper route entry projections:
  `type_theory_atlas_public_release_paper_route_entry_gives_stage1_unified_syntax`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage2_mltt`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage3_utt`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage4_tdtt_typing`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage4_tdtt_dashboard`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage5_system_embeddings`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage5_translation_reliability`,
  `type_theory_atlas_public_release_paper_route_entry_gives_stage6_metatheory`, and
  `type_theory_atlas_public_release_paper_route_entry_gives_paper_statement`.
- Build status checks:
  `make check`, which runs the environment check, README entry consistency
  check, top-level entry sync check across the README overview, Build Status
  Summary, and Metatheory.v, daily facade entry check, daily facade projection
  check, project stage-route check, daily release certificate check, daily
  report conclusion check, daily final report index check, daily final
  stage-route check, daily final stage-sync check, daily automation summary
  check, daily automation report-complete check, daily automation report
  stage-order check, daily automation report sync check, public release
  manifest check, public release manifest stage-sync check, public release
  complete certificate check, public release complete entry projection check,
  public release paper route check, public release paper route entry projection
  check, public GitHub homepage snippet check, public GitHub repository sync
  check, public release citation sync check, public README release package
  check, public release final entry check, public README release map check,
  public release navigation check, public release checklist check, public
  source hygiene check, public release final package check, file-order check,
  clean rebuild, and unfinished-proof scan.
  The public README release package check covers the public release manifest,
  public release manifest stage field/projection order, public release complete
  certificate, public release complete entry projections, public release paper
  route, public release paper route entry projections, homepage summary,
  homepage verification note, GitHub homepage snippet, GitHub repository sync,
  public release citation, and citation sync.
  The public release final package check additionally covers the final public
  release entry, public README release map, public README navigation, public
  release checklist, public source hygiene, expanded verification form,
  help/README target sync, and phony/help target sync.

This project develops a shared Coq framework for:

1. Martin-Lof Type Theory (MLTT)
2. Unified Type Theory (UTT)
3. Temporal Dependent Type Theory (TDTT)

The implementation proceeds in small verified stages:

1. shared syntax framework
2. MLTT typing rules
3. UTT extensions
4. TDTT temporal extensions
5. translations between systems
6. metatheory

## Current Stage

### Layer Summary

- Unified syntax and shared operations:
  `Syntax.v`, `Ops.v`, `Context.v`, and `DefEq.v`.
- MLTT layer:
  `MLTT.v`, `Weakening.v`, and `Substitution.v`.
- UTT layer:
  `UTT.v`, `UTTWeakening.v`, and `UTTSubstitution.v`.
- TDTT layer:
  `TemporalContext.v`, `TDTT.v`, `TDTTWeakening.v`,
  `TDTTSubstitution.v`, `TDTTTemporalWeakening.v`,
  `TDTTTemporalSubstitution.v`, and `DelayedSubstitution.v`.
- System translations:
  `Translations.v`.
- Metatheory and proof packaging:
  `Inversion.v` and `Metatheory.v`.

`theories/Atlas/Syntax.v` defines a common term language and explicit system
profiles. MLTT and UTT reject temporal syntax, while TDTT admits it. This keeps
the syntax representation shared without silently treating temporal terms as
ordinary MLTT terms. It also includes a native delayed-substitution syntax
constructor for TDTT clock instantiation, rejected by MLTT and UTT.

`theories/Atlas/Ops.v` defines shifting and substitution separately for ordinary
term variables and temporal variables. The two namespaces can therefore evolve
independently as the typing rules are added, including the binding behavior of
native delayed substitutions.

`theories/Atlas/Context.v` defines ordinary De Bruijn contexts and lookup.

`theories/Atlas/DefEq.v` defines shared definitional equality, including beta
reduction, dependent-pair projections, guarded fixed-point unfolding,
native delayed-substitution computation, congruence, and equivalence closure.

`theories/Atlas/MLTT.v` defines the initial MLTT typing judgment for universes,
dependent functions, dependent pairs, intensional identity types, and
conversion along definitional equality.

`theories/Atlas/Weakening.v` defines insertion into contexts, proves the
required De Bruijn shift algebra, and establishes MLTT weakening for lookups
and complete typing derivations.

`theories/Atlas/Substitution.v` develops the complementary De Bruijn
substitution algebra and the MLTT substitution theorem.

`theories/Atlas/UTT.v` adds the first Unified Type Theory layer: an
impredicative propositional sort, predicative type universes, cumulative
lifting, sorted products and strong sums, and a proved embedding of MLTT
derivations into UTT.

`theories/Atlas/UTTWeakening.v` and `theories/Atlas/UTTSubstitution.v` lift the
shared De Bruijn algebra to UTT and prove weakening and substitution for
complete UTT typing derivations.

`theories/Atlas/TemporalContext.v` introduces an independent De Bruijn context
for abstract time parameters. `theories/Atlas/TDTT.v` adds the first TDTT
typing layer: temporal indexing, a later type former, next introduction, a
guarded fixed-point rule, explicitly clock-indexed variants of later, next,
and guarded fix, `forall clock` products, clock abstraction, clock
application, and a proved embedding of UTT derivations into TDTT.
The native delayed-substitution constructor is typed by instantiating a body
from a fresh clock scope with a concrete well-formed clock.

`theories/Atlas/TDTTWeakening.v` and `theories/Atlas/TDTTSubstitution.v` prove
weakening and substitution for ordinary term variables in complete TDTT
typing derivations while keeping the temporal context fixed.

`theories/Atlas/TDTTTemporalWeakening.v` proves weakening for temporal
parameters, including the required interaction between temporal shifts,
ordinary substitutions, contexts, lookups, and definitional equality.

`theories/Atlas/TDTTTemporalSubstitution.v` proves substitution for temporal
parameters and lifts it from temporal lookups to complete TDTT typing
derivations.

`theories/Atlas/DelayedSubstitution.v` introduces the first delayed
substitution interface for TDTT clock instantiation. It represents delayed
substitution as top-clock temporal substitution, proves syntax-support,
context-preservation, typing-preservation, native delayed-substitution typing,
and connects clock beta reduction to the delayed-substitution operation.

`theories/Atlas/Translations.v` packages the inclusion translations
`MLTT -> UTT -> TDTT`, proves syntax-support monotonicity, and derives the
preservation of contexts, typing derivations, and definitional equalities
across each inclusion edge and the direct `MLTT -> TDTT` composite.

`theories/Atlas/Metatheory.v` proves syntax-support reliability: every
well-formed context entry, typable term, and derived type is admitted by the
feature profile of its object theory. It also packages translation reliability
and regularity lemmas, combining target-context well-formedness, typing
preservation, definitional-equality preservation, and target-system syntax
support, plus typed conversion and typed definitional-equality regularity
packages for all three systems, and context-extension regularity packages for
well-formed contexts, ordinary context lookups, TDTT temporal lookups, and
TDTT's temporal constructors.

`theories/Atlas/Inversion.v` adds regularity and inversion lemmas for typing
contexts, abstract time parameters, TDTT's temporal constructors, and guarded
fixed points, including the native delayed-substitution constructor.

## Verified Metatheory

The current Atlas development is summarized by the paper-facing theorem
`type_theory_atlas_paper_statement_holds` in `theories/Atlas/Metatheory.v`,
with `type_theory_atlas_main_theorem_holds` as the foundational main theorem.
It packages reusable interfaces across the staged route:

### Quick Stage Index

For daily automation reports, the strongest paper-ready entry point is
`type_theory_atlas_automation_done_dashboard_certificate_holds`, which
packages the shortest automation-complete entry with the final public theorem,
six stage-route projections, main theorem, and paper-facing statement. The
shorter `type_theory_atlas_automation_done_holds` remains the minimal
automation-complete entry.
The paper-ready automation archive certificate remains
`type_theory_atlas_paper_ready_automation_archive_certificate_holds`. The paper-ready project-cover certificate remains
`type_theory_atlas_paper_ready_project_cover_certificate_holds`. The paper-ready delivery certificate remains
`type_theory_atlas_paper_ready_delivery_certificate_holds`. The paper-ready
final report certificate remains
`type_theory_atlas_paper_ready_final_report_certificate_holds`. The paper-ready abstract-final
certificate remains `type_theory_atlas_paper_ready_abstract_final_certificate_holds`.
The paper-ready four-sentence index remains
`type_theory_atlas_paper_ready_four_sentence_index_holds`, the paper-ready
abstract certificate remains `type_theory_atlas_paper_ready_abstract_certificate_holds`,
the paper-ready claim index remains `type_theory_atlas_paper_ready_claim_index_holds`, and the
paper-ready completion certificate remains
`type_theory_atlas_paper_ready_completion_certificate_holds`, and the daily
report conclusion remains `type_theory_atlas_daily_report_conclusion_holds`.
The release certificate remains
`type_theory_atlas_daily_release_certificate_holds`, the daily report facade
remains `type_theory_atlas_daily_report_facade_holds`, and the foundational
daily-complete theorem remains `type_theory_atlas_daily_complete`.

The staged route is:

- Unified syntax framework: `type_theory_atlas_coverage_holds`,
  `atlas_feature_boundary_summary_holds`, `atlas_system_comparison_matrix_holds`,
  `type_theory_atlas_phase_order_gives_unified_syntax_framework`,
  `type_theory_atlas_daily_completion_gives_unified_syntax`, and
  `type_theory_atlas_daily_release_gives_unified_syntax`.
- MLTT: `type_theory_atlas_phase_order_gives_mltt_typing_support` and
  `type_theory_atlas_daily_release_gives_mltt`.
- UTT: `type_theory_atlas_phase_order_gives_utt_typing_support` and
  `type_theory_atlas_daily_release_gives_utt`.
- TDTT: `type_theory_atlas_phase_order_gives_tdtt_typing_support`,
  `atlas_tdtt_regularity_dashboard_holds`,
  `tdtt_delayed_substitution_regularities_hold`, and
  `type_theory_atlas_daily_release_gives_tdtt_typing`.
- System translations: `atlas_system_embedding_regularities_hold`,
  `type_theory_atlas_phase_order_gives_system_embeddings`,
  `type_theory_atlas_daily_release_gives_system_embeddings`,
  `atlas_translation_reliability_summary_holds`,
  `type_theory_atlas_phase_order_gives_translation_reliability`, and
  `type_theory_atlas_daily_release_gives_translation`.
- Metatheory and delivery: `type_theory_atlas_daily_complete`,
  `type_theory_atlas_phase_order_gives_main_theorem`,
  `type_theory_atlas_daily_release_gives_metatheory`,
  `type_theory_atlas_complete`, `type_theory_atlas_final_delivery_index_holds`,
  `type_theory_atlas_paper_claim_index_holds`, and
  `type_theory_atlas_daily_release_certificate_holds`.
  The release-level route consistency handle is
  `type_theory_atlas_daily_release_stage_consistency_holds`.

The detailed interface catalog remains below.

1. `type_theory_atlas_coverage_holds`
   states representative coverage facts for the MLTT, UTT, and TDTT syntax
   profiles, including which systems accept or reject propositions, temporal
   syntax, guarded fixed points, clock quantification, and native delayed
   substitutions.
2. `atlas_system_boundary_regularities_hold`
   packages syntax-support monotonicity along `MLTT -> UTT -> TDTT` and the
   concrete feature-boundary facts separating the three systems.
3. `atlas_feature_boundary_summary_holds`
   packages the feature matrix for propositions, time variables, temporal
   operators, guarded fixed points, clock quantification, native delayed
   substitution, and the TDTT clock-beta redex, together with support
   monotonicity along inclusions.
4. `atlas_system_embedding_regularities_hold`
   packages context preservation, typing preservation, definitional-equality
   preservation, and supported definitional-equality regularity for
   `MLTT -> UTT`, `UTT -> TDTT`, and direct `MLTT -> TDTT`.
5. `type_theory_atlas_metatheory_regularities_hold`
   packages syntax-support reliability, translation regularity, TDTT context
   regularity, temporal regularity, typed conversion, typed definitional
   equality, and TDTT constructor regularity.
6. `atlas_tdtt_constructor_regularities_summary_holds`
   packages TDTT constructor regularity for temporal constructors, clock
   constructors, and the native delayed-substitution constructor.
7. `atlas_tdtt_regularity_dashboard_holds`
   packages a one-page TDTT regularity dashboard combining feature boundaries,
   translation reliability, constructor regularity, typed computation, delayed
   substitution, delayed-substitution translation, and the main metatheory
   regularity interface.
8. `tdtt_typed_computation_regularities_hold`
   packages typed computation regularity for ordinary beta, clock beta,
   native delayed-substitution computation, guarded fixed-point unfolding, and
   clocked guarded fixed-point unfolding.
9. `tdtt_delayed_substitution_regularities_hold`
   packages the derived delayed-substitution interface for TDTT clock
   instantiation, including syntax support, context preservation, context
   cancellation, typing preservation, clock-lambda application typing, native
   delayed-substitution typing, native delayed-substitution computation, the
   clock-beta connection, and agreement between clock application and the native
   delayed-substitution constructor, including typed agreement at the delayed
   result type, a regularity package for that typed agreement, and typed
   congruence regularity for the native delayed-substitution constructor, plus
   an inversion-facing regularity package for native delayed-substitution
   typing.
10. `atlas_delayed_substitution_translation_summary_holds`
   packages the delayed-substitution boundary and translation-facing summary:
   MLTT and UTT reject the native constructor, TDTT accepts and types it, support
   is monotone along `MLTT -> UTT -> TDTT`, and the TDTT computation and
   delayed-substitution regularity packages are available together.
11. `atlas_translation_reliability_summary_holds`
   packages translation reliability for contexts, context support, typing, and
   definitional equality across `MLTT -> UTT`, `UTT -> TDTT`, and direct
   `MLTT -> TDTT`.
12. `atlas_final_summary_holds`
   packages the final Atlas summary, collecting coverage, system boundaries,
   feature boundaries, the system comparison matrix, its projection summary,
   the comparison/translation linkage summary, translation reliability, system
   embeddings, metatheory, and the TDTT regularity dashboard.
13. `atlas_layered_metatheory_summary_holds`
   packages a paper-facing layered metatheory summary, separating core syntax
   coverage, system and feature boundaries, the system comparison matrix and
   its projections, the comparison/translation linkage, translation
   reliability, system embeddings, the TDTT layer, and the final Atlas summary.
14. `atlas_paper_contribution_summary_holds`
   packages a paper-facing contribution summary, combining the main theorem,
   system comparison matrix, comparison projections, the comparison/translation
   linkage, main-theorem corollaries, and layered-summary projections.
15. `atlas_system_comparison_matrix_holds`
   packages the explicit MLTT/UTT/TDTT comparison matrix for propositions,
   temporal syntax, guarded fixed points, clock quantification, native delayed
   substitution, and the TDTT clock-beta redex.
16. `atlas_system_comparison_projection_summary_holds`
   packages projection theorems from the comparison matrix for proposition,
   temporal, guarded-fix, clock, and delayed-substitution profiles.
17. `atlas_comparison_translation_linkage_summary_holds`
   packages the linkage between the comparison matrix and translation
   reliability: feature boundaries, system boundaries, comparison projections,
   support monotonicity, context-support preservation, and typing preservation
   across `MLTT -> UTT -> TDTT`.
18. `type_theory_atlas_final_paper_theorem_holds`
   packages the final paper theorem, collecting the main theorem, coverage,
   comparison matrix, comparison projections, comparison/translation linkage,
   translation reliability, TDTT dashboard, final summary, layered summary, and
   paper contribution summary.
19. `type_theory_atlas_final_paper_gives_*`
   packages direct projection corollaries from the final paper theorem for
   coverage, comparison, comparison projections, comparison/translation
   linkage, translation reliability, the TDTT dashboard, and the paper
   contribution summary.
20. `type_theory_atlas_completion_index_holds`
   packages the current completion index, collecting the main theorem, final
   paper theorem, paper contribution summary, final-paper projections, layered
   summary, and final summary.
21. `type_theory_atlas_completion_gives_*`
   packages direct projection corollaries from the completion index for the
   main theorem, final paper theorem, paper contribution summary, coverage,
   comparison, translation reliability, TDTT dashboard, layered summary, and
   final summary.
22. `type_theory_atlas_paper_statement_holds`
   packages a paper-style statement of the verified contribution: completion
   index, main theorem, final paper theorem, unified coverage, system
   comparison, translation reliability, TDTT dashboard, final summary, and
   paper contribution summary.
23. `type_theory_atlas_paper_statement_gives_*`
   packages direct projection corollaries from the paper-style statement for
   completion, main/final theorem, unified coverage, system comparison,
   translation reliability, TDTT dashboard, final summary, and contribution
   summary.
24. `type_theory_atlas_project_status_certificate_holds`
   packages the current project status certificate, collecting the paper-style
   statement, completion index, main/final theorem, unified coverage, system
   comparison, translation reliability, TDTT dashboard, final summary, and
   contribution summary.
25. `type_theory_atlas_status_gives_*`
   packages direct projection corollaries from the project status certificate
   for the paper-style statement, completion index, main/final theorem, unified
   coverage, system comparison, translation reliability, TDTT dashboard, final
   summary, and contribution summary.
26. `type_theory_atlas_release_summary_holds`
   packages the current release summary, collecting the project status
   certificate, paper-style statement, completion index, main/final theorem,
   unified coverage, system comparison, translation reliability, TDTT
   dashboard, final summary, and contribution summary.
27. `type_theory_atlas_release_gives_*`
   packages direct projection corollaries from the release summary for the
   project status certificate, paper-style statement, completion index,
   main/final theorem, unified coverage, system comparison, translation
   reliability, TDTT dashboard, final summary, and contribution summary.
28. `type_theory_atlas_artifact_index_holds`
   packages the current artifact index, aligning the release summary, project
   status certificate, paper-style statement, completion index, main/final
   theorem, unified coverage, system comparison, translation reliability, TDTT
   dashboard, final summary, and contribution summary.
29. `type_theory_atlas_artifact_gives_*`
   packages direct projection corollaries from the artifact index for the
   release summary, project status certificate, paper-style statement,
   completion index, main/final theorem, unified coverage, system comparison,
   translation reliability, TDTT dashboard, final summary, and contribution
   summary.
30. `type_theory_atlas_phase_order_certificate_holds`
   and `type_theory_atlas_phase_order_gives_*` package the automation-facing
   phase order: unified syntax framework, MLTT, UTT, TDTT, system translations,
   and final metatheory/artifact handles, with direct stage projections for
   MLTT/UTT/TDTT typing support, system embeddings, translation reliability,
   the TDTT dashboard, the main theorem, and the artifact index.
31. `type_theory_atlas_paper_section_map_holds`
   and `type_theory_atlas_paper_section_gives_*` map paper-facing sections to
   verified Coq handles for the introduction contribution, unified syntax,
   MLTT, UTT, TDTT, translations, metatheory, and artifact index.
32. `type_theory_atlas_writing_checklist_holds`
   and `type_theory_atlas_writing_checklist_gives_*` collect the section map,
   phase order, release summary, project status, artifact index, paper
   statement, main/final theorem, completion index, and contribution summary
   under one writing-facing certificate.
33. `type_theory_atlas_paper_claim_index_holds`
   and `type_theory_atlas_paper_claim_gives_*` collect the final paper claim:
   writing checklist, core statement, unified framework, system comparison,
   translation reliability, TDTT extension, metatheory, artifact index, release
   summary, and contribution summary.
34. `type_theory_atlas_final_delivery_index_holds`
   and `type_theory_atlas_final_delivery_gives_*` collect the final delivery
   state: paper-claim index, writing checklist, section map, phase order,
   release summary, project status, artifact index, paper statement,
   completion index, main/final theorem, final summary, and contribution
   summary.
35. `type_theory_atlas_complete`
   is the single top-level completion theorem for the current artifact. Its
   `type_theory_atlas_complete_gives_*` corollaries expose the paper-claim
   index, artifact index, and main theorem directly.
36. `type_theory_atlas_automation_daily_report_holds`
   and `type_theory_atlas_daily_report_gives_*` collect the complete entry,
   paper-claim index, artifact index, main theorem, phase order, writing
   checklist, release summary, project status, final summary, and contribution
   summary for daily automation reports.
37. `type_theory_atlas_daily_report_gives_*`
   also exposes the automation route directly: unified syntax framework,
   MLTT typing support, UTT typing support, TDTT typing support, TDTT
   dashboard, system embeddings, translation reliability, and metatheory.
38. `type_theory_atlas_daily_completion_certificate_holds`
   and `type_theory_atlas_daily_completion_gives_*` collect the daily report,
   complete entry, route projections, release summary, project status,
   artifact index, final summary, and metatheory handles into one daily
   completion certificate.
39. `type_theory_atlas_daily_complete`
   is the single top-level daily automation theorem. Its
   `type_theory_atlas_daily_complete_gives_*` corollaries expose the daily
   report, complete entry, route projections, artifact index, and metatheory
   directly.
40. `type_theory_atlas_daily_stage_route_index_holds`
   and `type_theory_atlas_daily_complete_gives_stage_route_index` package the
   daily-complete route projections into one stage-route index.
41. `type_theory_atlas_daily_phase_route_consistency_holds`
   and `type_theory_atlas_daily_complete_gives_phase_route_consistency`
   connect the daily stage-route index with the global phase-order
   certificate.
42. `type_theory_atlas_daily_phase_route_gives_*` exposes the unified syntax,
   MLTT, UTT, TDTT, system embedding, translation, metatheory, phase-order,
   stage-route, and artifact handles from that consistency certificate.
43. `type_theory_atlas_daily_final_route_certificate_holds`
   and `type_theory_atlas_daily_complete_gives_final_route_certificate`
   package the daily report, route consistency, phase order, stage route,
   artifact, and stage projection handles into one final route certificate.
44. `type_theory_atlas_daily_final_route_gives_*` exposes the final route
   certificate's report, completion, consistency, phase-order, stage-route,
   syntax, MLTT, UTT, TDTT, translation, metatheory, and artifact handles.
45. `type_theory_atlas_daily_automation_final_entry_index_holds`
   and `type_theory_atlas_daily_complete_gives_automation_final_entry_index`
   package the daily-complete endpoint, complete entry, final route, and
   stage projection handles into one final automation entry index.
46. `type_theory_atlas_daily_final_entry_gives_*` exposes the final entry
   index's completion, report, route, phase-order, stage-route, syntax, MLTT,
   UTT, TDTT, translation, metatheory, and artifact handles directly.
47. `type_theory_atlas_daily_deliverable_completion_certificate_holds`
   and `type_theory_atlas_daily_complete_gives_deliverable_completion`
   package the final automation entry index, project status, release summary,
   artifact index, route, stage projections, and metatheory into one daily
   deliverable certificate.
48. `type_theory_atlas_daily_deliverable_gives_*` exposes the daily
   deliverable certificate's final entry, completion, route, release, status,
   artifact, syntax, MLTT, UTT, TDTT, translation, and metatheory handles.
49. `type_theory_atlas_daily_complete_gives_deliverable_*` exposes the same
   report-facing deliverable handles directly from the daily-complete entry
   point.
50. `type_theory_atlas_daily_report_facade_holds`
   and `type_theory_atlas_daily_complete_gives_report_facade` package the
   daily-complete endpoint, deliverable certificate, release/status/artifact
   handles, route handles, and stage projections into one daily report facade.
51. `type_theory_atlas_daily_report_facade_gives_*` exposes the facade's
   entry point, deliverable certificate, release/status/artifact handles,
   stage projections, translations, and metatheory directly.
52. `type_theory_atlas_daily_release_certificate_holds`
   and `type_theory_atlas_daily_report_facade_gives_release_certificate`
   package the facade, stage-route index, phase-order certificate, final
   delivery index, paper-claim index, paper statement, and main theorem into a
   single daily release certificate.
53. `type_theory_atlas_daily_release_gives_*` exposes the release
   certificate's facade, stage route, phase order, final delivery, paper claim,
   paper statement, and main theorem handles directly.
54. `type_theory_atlas_daily_release_gives_unified_syntax`,
   `type_theory_atlas_daily_release_gives_mltt`,
   `type_theory_atlas_daily_release_gives_utt`,
   `type_theory_atlas_daily_release_gives_tdtt_typing`,
   `type_theory_atlas_daily_release_gives_system_embeddings`,
   `type_theory_atlas_daily_release_gives_translation`, and
   `type_theory_atlas_daily_release_gives_metatheory` expose the requested
   six-stage automation route from the daily release certificate.
55. `type_theory_atlas_daily_release_stage_consistency_holds`
   and `type_theory_atlas_daily_release_gives_stage_consistency` package the
   release certificate, its stage-route index, and the stage-route index
   rebuilt from the release certificate's phase-order field into one
   consistency handle.
56. `type_theory_atlas_daily_release_stage_consistency_gives_*` exposes the
   consistency handle's release certificate, stored route, phase-built route,
   phase order, unified syntax, MLTT, UTT, TDTT, system translation, and
   metatheory handles directly.
57. `type_theory_atlas_daily_report_conclusion_holds`
   and `type_theory_atlas_daily_release_gives_report_conclusion` package the
   release certificate, release-stage consistency, six-stage route, metatheory,
   and paper-facing statement into one short daily report conclusion.
58. `type_theory_atlas_daily_report_conclusion_gives_*` exposes the conclusion's
   release certificate, consistency handle, unified syntax, MLTT, UTT, TDTT,
   system translation, metatheory, and paper-facing statement directly.
59. `type_theory_atlas_daily_conclusion_stage_order_summary_holds`
   and `type_theory_atlas_daily_report_conclusion_gives_stage_order_summary`
   package the daily report conclusion into an explicit stage1-to-stage6
   summary matching the requested automation route.
60. `type_theory_atlas_daily_conclusion_stage_order_gives_*` exposes that
   ordered summary's conclusion, unified syntax, MLTT, UTT, TDTT, system
   embeddings, translation reliability, metatheory, and paper-facing statement.
61. `type_theory_atlas_daily_final_report_index_holds`
   and `type_theory_atlas_daily_report_conclusion_gives_final_report_index`
   package the daily report conclusion, stage-order summary, release
   certificate, stage consistency, metatheory, and paper-facing statement into
   the final daily report index.
62. `type_theory_atlas_daily_final_report_gives_*` exposes the final report
   index's conclusion, stage-order summary, release certificate, stage
   consistency, metatheory, and paper-facing statement directly.
63. `type_theory_atlas_daily_final_report_gives_stage1_*` through
   `type_theory_atlas_daily_final_report_gives_stage6_*` expose the complete
   ordered route directly from the final daily report index.
64. `type_theory_atlas_daily_final_stage_sync_certificate_holds`
   and `type_theory_atlas_daily_final_report_gives_stage_sync_certificate`
   package the final report index, its stage-order summary, and all final
   stage projections into one Coq-level sync certificate.
65. `type_theory_atlas_daily_automation_summary_certificate_holds`
   and `type_theory_atlas_daily_final_report_gives_automation_summary_certificate`
   package the final report index, stage-sync certificate, release summary,
   project status, metatheory, and paper-facing statement into one daily
   automation summary certificate.
66. `type_theory_atlas_daily_automation_summary_gives_*` exposes the summary's
   final report, stage-sync certificate, conclusion, release certificate,
   facade, daily-complete certificate, artifact completion, release summary,
   project status, metatheory, and paper-facing statement directly.
67. `type_theory_atlas_daily_automation_summary_gives_stage1_*` through
   `type_theory_atlas_daily_automation_summary_gives_stage6_*` expose the full
   requested route directly from the daily automation summary certificate.
68. `type_theory_atlas_daily_automation_stage_route_certificate_holds`
   and `type_theory_atlas_daily_automation_summary_gives_stage_route_certificate`
   package the daily automation summary together with its final stage-sync
   certificate and complete stage route.
69. `type_theory_atlas_daily_automation_stage_route_gives_*` exposes that
   certificate's summary, final stage-sync certificate, and full stage1-to-stage6
   route directly.
70. `type_theory_atlas_daily_final_dashboard_certificate_holds`
   and `type_theory_atlas_daily_automation_summary_gives_final_dashboard`
   package the automation summary, stage-route certificate, final report,
   release summary, project status, metatheory, and paper-facing statement into
   the current final daily dashboard.
71. `type_theory_atlas_daily_final_dashboard_gives_*` exposes the dashboard's
   automation summary, stage-route certificate, final report, final stage-sync
   certificate, release summary, project status, metatheory, and paper-facing
   statement directly.
72. `type_theory_atlas_daily_final_dashboard_gives_stage1_*` through
   `type_theory_atlas_daily_final_dashboard_gives_stage6_*` expose the full
   requested route directly from the current final daily dashboard.
73. `type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds`
   and `type_theory_atlas_daily_final_dashboard_gives_stage_route_certificate`
   package the final dashboard itself together with its dashboard-level
   stage-route certificate and stage1-to-stage6 projections.
74. `type_theory_atlas_daily_final_dashboard_stage_route_gives_*` exposes that
   final route certificate's dashboard, dashboard-level stage-route certificate,
   and full stage1-to-stage6 route directly.
75. `type_theory_atlas_daily_final_dashboard_completion_certificate_holds`
   and `type_theory_atlas_daily_final_dashboard_gives_completion_certificate`
   package the final dashboard, final dashboard stage-route certificate, final
   report, release summary, project status, metatheory, and paper-facing
   statement into the current highest daily completion handle.
76. `type_theory_atlas_daily_final_dashboard_completion_gives_*` exposes that
   completion handle's dashboard, final stage-route certificate, automation
   summary, final report, release summary, project status, metatheory, and
   paper-facing statement directly.
77. `type_theory_atlas_daily_final_dashboard_completion_gives_stage1_*`
   through `type_theory_atlas_daily_final_dashboard_completion_gives_stage6_*`
   expose the full requested route directly from the current highest daily
   completion handle.
78. `type_theory_atlas_paper_ready_completion_certificate_holds` and
   `type_theory_atlas_daily_final_dashboard_completion_gives_paper_ready_certificate`
   package the current highest completion handle, final dashboard, complete
   stage route, system translations, metatheory, and paper-facing statement
   into a single paper-ready certificate.
79. `type_theory_atlas_paper_ready_completion_gives_*` exposes that
   paper-ready certificate's completion handle, dashboard, stage route,
   unified syntax, MLTT, UTT, TDTT, system embedding, translation, metatheory,
   and paper-facing statement directly.
80. `type_theory_atlas_paper_ready_claim_index_holds` and
   `type_theory_atlas_paper_ready_completion_gives_claim_index` package the
   current paper-ready completion certificate together with the paper claim
   index, final paper theorem, contribution summary, system comparison,
   translation, TDTT dashboard, and metatheory.
81. `type_theory_atlas_paper_ready_claim_gives_*` exposes that paper-ready
   claim index's completion certificate, claim index, paper statement, final
   paper theorem, contribution summary, system comparison, translation, TDTT
   dashboard, and metatheory directly.
82. `type_theory_atlas_paper_ready_abstract_certificate_holds` and
   `type_theory_atlas_paper_ready_claim_gives_abstract_certificate` package the
   paper-ready abstract-level contribution route: unified framework, MLTT, UTT,
   TDTT typing, TDTT dashboard, translation, metatheory, and paper-facing
   statement.
83. `type_theory_atlas_paper_ready_abstract_gives_*` exposes that abstract
   certificate's claim index, completion certificate, unified framework, MLTT,
   UTT, TDTT, translation, metatheory, and paper-facing statement directly.
84. `type_theory_atlas_paper_ready_four_sentence_index_holds` and
   `type_theory_atlas_paper_ready_abstract_gives_four_sentence_index` package
   the paper abstract into four proof handles: unified framework, three-system
   coverage, system translations, and metatheory, plus the paper-facing
   statement.
85. `type_theory_atlas_paper_ready_four_sentence_gives_*` exposes that
   four-sentence index's unified framework, three-system coverage,
   translations, metatheory, and paper-facing statement directly.
86. `type_theory_atlas_paper_ready_abstract_sentence_1_*` through
   `type_theory_atlas_paper_ready_abstract_sentence_4_*` expose the four
   abstract sentences as short corollaries for unified framework, three-system
   coverage, translations, and metatheory.
87. `type_theory_atlas_paper_ready_abstract_final_certificate_holds` and
   `type_theory_atlas_paper_ready_four_sentence_gives_abstract_final_certificate`
   package the four-sentence index, the four short abstract sentence handles,
   and the paper-facing statement into the current abstract-final certificate.
88. `type_theory_atlas_paper_ready_abstract_final_gives_*` exposes that
   abstract-final certificate's four-sentence index, four abstract sentences,
   and paper-facing statement directly.
89. `type_theory_atlas_paper_ready_final_report_certificate_holds` and
   `type_theory_atlas_paper_ready_abstract_final_gives_final_report_certificate`
   package the abstract-final certificate, daily final dashboard completion,
   final report index, dashboard, stage route, four-sentence index,
   metatheory, and paper-facing statement into one report-level certificate.
90. `type_theory_atlas_paper_ready_final_report_gives_*` exposes that
   report-level certificate's abstract-final certificate, daily completion,
   daily report, dashboard, stage route, four-sentence index, metatheory, and
   paper-facing statement directly.
91. `type_theory_atlas_paper_ready_delivery_certificate_holds` and
   `type_theory_atlas_paper_ready_final_report_gives_delivery_certificate`
   package the paper-ready final report certificate, daily completion, release
   summary, project status, dashboard, abstract-final certificate,
   four-sentence index, metatheory, and paper-facing statement into the current
   delivery certificate.
92. `type_theory_atlas_paper_ready_delivery_gives_*` exposes that delivery
   certificate's final report, daily completion, release summary, project
   status, dashboard, abstract-final certificate, four-sentence index,
   metatheory, and paper-facing statement directly.
93. `type_theory_atlas_paper_ready_project_cover_certificate_holds` and
   `type_theory_atlas_paper_ready_delivery_gives_project_cover_certificate`
   package the delivery certificate, paper-facing statement, core contribution,
   abstract-final certificate, four-sentence index, release summary, project
   status, daily completion, validation dashboard, and metatheory into the
   current project-cover certificate.
94. `type_theory_atlas_paper_ready_project_cover_gives_*` exposes that
   project-cover certificate's delivery certificate, paper-facing statement,
   core contribution, abstract-final certificate, four-sentence index, release
   summary, project status, daily completion, validation dashboard, and
   metatheory directly.
95. `type_theory_atlas_paper_ready_automation_archive_certificate_holds` and
   `type_theory_atlas_paper_ready_project_cover_gives_automation_archive_certificate`
   package the project-cover certificate, delivery certificate, daily
   completion, automation summary, final dashboard, release summary, project
   status, stage route, metatheory, and paper-facing statement into the current
   automation archive certificate.
96. `type_theory_atlas_paper_ready_archive_gives_*` exposes that automation
   archive certificate's project cover, delivery certificate, daily completion,
   automation summary, final dashboard, release summary, project status, stage
   route, metatheory, and paper-facing statement directly.
97. `type_theory_atlas_paper_ready_automation_complete_certificate_holds` and
   `type_theory_atlas_paper_ready_archive_gives_automation_complete_certificate`
   package the automation archive, project-cover certificate, delivery
   certificate, four-sentence index, daily completion, automation summary,
   final dashboard, stage route, metatheory, and paper-facing statement into
   the current automation-complete certificate.
98. `type_theory_atlas_paper_ready_complete_gives_*` exposes that
   automation-complete certificate's archive, project cover, delivery
   certificate, four-sentence index, daily completion, automation summary,
   final dashboard, stage route, metatheory, and paper-facing statement
   directly.
99. `type_theory_atlas_public_entry_holds` and
   `type_theory_atlas_public_entry_gives_*` provide the short public Atlas
   entry and recover the automation-complete certificate, daily completion,
   automation summary, final dashboard, stage route, unified syntax, MLTT,
   UTT, TDTT typing, TDTT dashboard, system embeddings, translation
   reliability, main theorem, and paper-facing statement from it.
100. `type_theory_atlas_public_route_certificate_holds` packages the public
   entry with unified syntax, MLTT, UTT, TDTT typing, the TDTT dashboard,
   system embeddings, translation reliability, the main theorem, and the
   paper-facing statement.
101. `type_theory_atlas_public_route_gives_*` exposes that public route
   certificate's entry, unified syntax, MLTT, UTT, TDTT typing, TDTT dashboard,
   system embeddings, translation reliability, main theorem, and paper-facing
   statement directly.
102. `type_theory_atlas_public_theorem_holds` provides the short paper-facing
   theorem alias for the public route certificate, with direct projections back
   to the route certificate, unified syntax, MLTT, UTT, TDTT typing, TDTT
   dashboard, system embeddings, translation reliability, main theorem, and
   paper-facing statement.
103. `type_theory_atlas_public_summary_certificate_holds` packages the public
   theorem, public route certificate, main theorem, and paper-facing statement
   into a compact summary certificate for paper and README references.
104. `type_theory_atlas_public_summary_gives_*` exposes that summary
   certificate's public theorem, route certificate, unified syntax, MLTT, UTT,
   TDTT typing, TDTT dashboard, system embeddings, translation reliability,
   main theorem, and paper-facing statement directly.
105. `type_theory_atlas_public_delivery_certificate_holds` packages the public
   summary, public theorem, public route certificate, unified syntax, MLTT,
   UTT, TDTT typing, TDTT dashboard, system embeddings, translation
   reliability, main theorem, and paper-facing statement into the current
   delivery-level certificate.
106. `type_theory_atlas_public_delivery_gives_*` exposes that delivery-level
   certificate's summary, public theorem, public route, unified syntax, MLTT,
   UTT, TDTT typing, TDTT dashboard, system embeddings, translation
   reliability, main theorem, and paper-facing statement directly.
107. `type_theory_atlas_public_final_certificate_holds` packages the public
   delivery certificate, public summary, public theorem, public route, public
   entry, main theorem, and paper-facing statement into the current final
   public certificate.
108. `type_theory_atlas_public_final_gives_*` exposes that final public
   certificate's delivery certificate, summary, public theorem, public route,
   public entry, unified syntax, MLTT, UTT, TDTT typing, TDTT dashboard,
   system embeddings, translation reliability, main theorem, and paper-facing
   statement directly.
109. `type_theory_atlas_final_public_theorem_holds` provides the single final
   public theorem alias for the public final certificate, with direct
   projections back to the final certificate, unified syntax, MLTT, UTT, TDTT
   typing, TDTT dashboard, system embeddings, translation reliability, main
   theorem, and paper-facing statement.
110. `type_theory_atlas_automation_done_holds` provides the shortest
   automation-complete entry and projects back to the final public theorem,
   unified syntax, MLTT, UTT, TDTT typing, TDTT dashboard, system embeddings,
   translation reliability, main theorem, and paper-facing statement.
111. `type_theory_atlas_automation_done_dashboard_certificate_holds` packages
   automation done, the final public theorem, unified syntax, MLTT, UTT, TDTT
   typing, TDTT dashboard, system embeddings, translation reliability, main
   theorem, and paper-facing statement into the current automation dashboard.
112. `type_theory_atlas_automation_dashboard_gives_*` exposes that automation
   dashboard's done entry, final public theorem, unified syntax, MLTT, UTT,
   TDTT typing, TDTT dashboard, system embeddings, translation reliability,
   main theorem, and paper-facing statement directly.
113. `type_theory_atlas_daily_automation_report_complete_holds` provides the
   daily automation report-complete entry point, with projections back to the
   dashboard, automation-done entry, final public theorem, and the staged route
   from unified syntax through MLTT, UTT, TDTT, translations, and metatheory.
114. `type_theory_atlas_public_release_manifest_holds` packages the daily
   report-complete entry, dashboard, final public theorem, final public
   certificate, staged route, metatheory, and paper-facing statement into one
   public release manifest for paper and homepage references.

More concretely, the development proves:

1. ordinary-variable weakening and substitution for MLTT, UTT, and TDTT;
2. temporal-parameter weakening and substitution for TDTT;
3. preservation of shared definitional equality under ordinary and temporal
   variable operations;
4. inclusion translations `MLTT -> UTT -> TDTT`, including context, typing,
   and definitional-equality preservation on each edge and on the direct
   `MLTT -> TDTT` composite;
5. a unified feature-boundary matrix for propositions, temporal syntax,
   guarded fixed points, clock quantification, and native delayed substitution;
6. syntax-support reliability for all three typing judgments;
7. typed conversion and typed definitional-equality regularity packages for
   MLTT, UTT, and TDTT;
8. context-extension and context-lookup regularity packages for all three
   systems;
9. TDTT temporal lookup and temporal well-formedness regularity;
10. TDTT temporal-constructor regularity for `At`, `LaterAt`, `NextAt`, and
   `FixAt`;
11. TDTT clock-constructor regularity for `ClockPi`, `ClockLam`, and
    `ClockApp`, plus native delayed-substitution constructor regularity;
12. a TDTT constructor regularity summary that packages temporal constructors,
    clock constructors, and native delayed substitution under one interface;
13. a TDTT regularity dashboard that combines feature boundaries, translation
    reliability, constructor regularity, typed computation, delayed
    substitution, delayed-substitution translation, and metatheory regularity;
14. typed computation regularity for beta, clock beta, guarded fix unfolding,
    native delayed-substitution computation, and clocked guarded fix unfolding;
15. a first TDTT delayed-substitution interface for clock instantiation,
    including native syntax support, context cancellation, typing preservation,
    native delayed-substitution typing, native delayed-substitution
    computation, the delayed result type of clock-lambda application, and the
    typed definitional agreement between clock application and native delayed
    substitution, packaged with context, typing, and syntax-support regularity,
    plus native delayed-substitution congruence and inversion regularity.
16. a delayed-substitution translation-facing summary that combines system
    boundary facts, support monotonicity along inclusions, concrete TDTT native
    typing, native computation, typed computation regularity, and the full
    delayed-substitution regularity interface.
17. a translation reliability summary for all three inclusion paths, covering
    context preservation, context-support preservation, typing regularity, and
    supported definitional-equality regularity.
18. a final Atlas summary that aggregates coverage, system boundaries, feature
    boundaries, translation reliability, system embeddings, metatheory, and the
    TDTT regularity dashboard.
19. a layered metatheory summary that separates the Atlas result into core
    coverage, boundaries, translations and embeddings, the TDTT-specific layer,
    and the final summary.
20. projection theorems from the layered summary for core coverage, translation
    reliability, the TDTT dashboard, and the final Atlas summary.
21. corollaries from the main theorem for translation reliability, the TDTT
    dashboard, the final Atlas summary, and the layered metatheory summary.
22. a paper contribution summary that combines the main theorem, its direct
    corollaries, and projection theorems from the layered summary.
23. an explicit system comparison matrix for MLTT, UTT, and TDTT feature
    support and rejection facts.
24. projection theorems from the system comparison matrix for proposition,
    temporal, guarded-fix, clock, and delayed-substitution feature profiles.
25. a comparison/translation linkage summary connecting the system comparison
    matrix with support, context-support, and typing preservation across
    inclusion translations.
26. a final paper theorem that gathers the main theorem, coverage, comparison
    matrix and projections, comparison/translation linkage, translation
    reliability, TDTT dashboard, final summary, layered summary, and paper
    contribution summary.
27. projection corollaries from the final paper theorem for coverage,
    comparison, comparison projections, comparison/translation linkage,
    translation reliability, the TDTT dashboard, and the paper contribution
    summary.
28. a completion index that ties together the main theorem, final paper theorem,
    paper contribution summary, final-paper projections, layered summary, and
    final summary.
29. projection corollaries from the completion index for the main theorem,
    final paper theorem, paper contribution summary, coverage, comparison,
    translation reliability, TDTT dashboard, layered summary, and final summary.
30. a paper-style theorem statement that compresses the verified contribution
    into completion, main/final theorem, unified coverage, system comparison,
    translation reliability, TDTT dashboard, final summary, and contribution
    summary components.
31. projection corollaries from the paper-style statement for completion,
    main/final theorem, unified coverage, system comparison, translation
    reliability, TDTT dashboard, final summary, and contribution summary.
32. a project status certificate that gathers the paper-style statement,
    completion index, main/final theorem, unified coverage, system comparison,
    translation reliability, TDTT dashboard, final summary, and contribution
    summary.
33. projection corollaries from the project status certificate for the
    paper-style statement, completion index, main/final theorem, unified
    coverage, system comparison, translation reliability, TDTT dashboard, final
    summary, and contribution summary.
34. a release summary that gathers the project status certificate, paper-style
    statement, completion index, main/final theorem, unified coverage, system
    comparison, translation reliability, TDTT dashboard, final summary, and
    contribution summary.
35. projection corollaries from the release summary for the project status
    certificate, paper-style statement, completion index, main/final theorem,
    unified coverage, system comparison, translation reliability, TDTT
    dashboard, final summary, and contribution summary.
36. an artifact index that aligns the release summary, project status
    certificate, paper-style statement, completion index, main/final theorem,
    unified coverage, system comparison, translation reliability, TDTT
    dashboard, final summary, and contribution summary.
37. projection corollaries from the artifact index for the release summary,
    project status certificate, paper-style statement, completion index,
    main/final theorem, unified coverage, system comparison, translation
    reliability, TDTT dashboard, final summary, and contribution summary.
38. a phase-order certificate that follows the automation route from unified
    syntax, through MLTT, UTT, TDTT, and translations, to the final metatheory
    and artifact index, together with direct stage-completion projections.
39. a paper-section map that points each paper-facing section to a verified Coq
    handle for the contribution, unified syntax, MLTT, UTT, TDTT,
    translations, metatheory, and artifact index.
40. a writing checklist that collects the paper-section map, phase-order
    certificate, release summary, project status, artifact index, paper
    statement, main/final theorem, completion index, and contribution summary.
41. a paper-claim index that gathers the final paper-facing claim around the
    writing checklist, core statement, unified framework, system comparison,
    translation reliability, TDTT extension, metatheory, artifact/release
    handles, and contribution summary.
42. a final delivery index that gathers the paper-claim index, writing
    checklist, section map, phase order, release summary, project status,
    artifact index, paper statement, completion index, main/final theorem,
    final summary, and contribution summary.
43. a single complete entry point that proves the final delivery index and
    exposes the paper-claim index, artifact index, and main theorem directly.
44. an automation daily-report certificate that collects the complete entry,
    paper-claim index, artifact index, main theorem, phase order, writing
    checklist, release summary, project status, final summary, and contribution
    summary.
45. direct daily-report route projections for unified syntax, MLTT, UTT, TDTT,
    system embeddings, translation reliability, and metatheory.
46. a daily completion certificate that gathers the daily report, complete
    entry, route projections, release summary, project status, artifact index,
    final summary, and metatheory handles.
47. a single daily-complete entry point that proves the daily completion
    certificate and exposes the daily report, complete entry, artifact index,
    and metatheory directly.
48. a daily stage-route index that packages the daily-complete route handles
    for unified syntax, MLTT, UTT, TDTT, system embeddings, translations, and
    metatheory.
49. a daily phase-route consistency certificate that rebuilds the daily
    stage-route index from the global phase-order certificate and the
    daily-complete endpoint.
50. direct daily phase-route projection corollaries for unified syntax, MLTT,
    UTT, TDTT, system embeddings, translations, metatheory, phase order,
    stage-route index, and artifact index.
51. a daily final-route certificate that collects the report, daily-complete
    endpoint, phase consistency, phase order, stage-route index, all major
    stage projections, metatheory, and artifact index.
52. direct daily final-route projection corollaries for report, completion,
    consistency, phase order, stage route, unified syntax, MLTT, UTT, TDTT,
    system embeddings, translations, metatheory, and artifact index.
53. a daily automation final-entry index that collects the daily-complete
    endpoint, complete entry, final route certificate, report, phase
    consistency, phase order, stage route, all major stage projections,
    metatheory, and artifact index.
54. direct daily final-entry projection corollaries for completion, report,
    final route, phase consistency, phase order, stage route, unified syntax,
    MLTT, UTT, TDTT, system embeddings, translations, metatheory, and artifact
    index.
55. a daily deliverable completion certificate that gathers the final
    automation entry index, release summary, project status, artifact index,
    phase route, stage projections, and metatheory into a single report-facing
    completion handle.
56. direct daily deliverable projection corollaries for final entry,
    completion, route, release summary, project status, artifact index,
    unified syntax, MLTT, UTT, TDTT, system embeddings, translations, and
    metatheory.
57. direct daily-complete deliverable projection corollaries that make
    `type_theory_atlas_daily_complete` the shortest entry point for release,
    status, artifact, stage-route, syntax, MLTT, UTT, TDTT, translations, and
    metatheory handles.
58. a daily report facade that gathers the daily-complete endpoint,
    deliverable completion certificate, final entry index, release summary,
    project status, artifact index, route handles, stage projections, and
    metatheory into one automation-facing entry.
59. direct daily report facade projection corollaries for the entry point,
    deliverable certificate, release summary, project status, artifact index,
    stage projections, translations, and metatheory.

A first delayed-substitution interface, native syntax constructor, native
typing rule, constructor regularity package, and typed computation rule are now
present. The delayed-substitution interface now also exposes typed agreement
regularity between clock application and native delayed substitution, and typed
congruence and inversion regularity for the native constructor. The current
translation-facing summary now connects those TDTT-local packages to the
MLTT/UTT/TDTT system boundary. A general feature-boundary summary now also
records the wider MLTT/UTT/TDTT capability matrix, and a translation reliability
summary centralizes the inclusion-preservation facts. A TDTT constructor summary
now centralizes temporal, clock, and native delayed-substitution constructor
regularity. A TDTT regularity dashboard now gives a compact top-level handle on
the major TDTT and translation summaries. An Atlas final summary now provides a
single top-level handle for the major verified interfaces. A layered metatheory
summary now exposes the same result in a paper-friendly structure. Projection
theorems now make its core coverage, translation reliability, TDTT dashboard,
and final-summary layers directly reusable. Main-theorem corollaries now expose
the translation, TDTT, final-summary, and layered-summary views directly from
`type_theory_atlas_main_theorem_holds`. A paper contribution summary now
collects the main theorem, those corollaries, and the layered-summary
projections under one reusable interface. An explicit system comparison matrix
now gives a compact feature table for MLTT, UTT, and TDTT. Projection theorems
now expose the matrix as separate proposition, temporal, guarded-fix, clock, and
delayed-substitution profiles. A comparison/translation linkage summary now
connects those boundary facts to support, context-support, and typing
preservation along the inclusion translations. A final paper theorem now
provides a single top-level entry point for the verified Atlas contribution.
Projection corollaries from that theorem now expose its major paper-facing
components directly. A completion index now ties together the main theorem,
final paper theorem, projections, layered summary, and final summary as the
project's current verified endpoint. Projection corollaries from that index now
make its main paper-facing components directly reusable. A paper-style theorem
statement now compresses those components into a concise final contribution
claim. Projection corollaries from that statement now expose its parts directly
for paper sections. A project status certificate now records the current
verified endpoint in Coq; the build checks below validate the external compile
status and absence of unfinished proof markers. Projection corollaries from the
status certificate now expose its verified components directly. A release
summary now provides a concise top-level handle for the current verified state.
Projection corollaries from the release summary now expose each release-level
component directly. An artifact index now aligns those release-level Coq
handles with the README-facing release and build-check story. Projection
corollaries from the artifact index now expose each artifact-level component
directly. A phase-order certificate now records the automation route as a
Coq-level theorem with direct handles for the artifact index, translation
reliability, system embeddings, MLTT/UTT/TDTT typing support, TDTT dashboard,
and main theorem. A paper-section map now turns that route into a writing
index, so each paper-facing section has a verified Coq handle. A writing
checklist now gathers the section map, phase order, release/status certificates,
artifact index, and main paper-facing theorems into one Coq-level handle. A
paper-claim index now packages the final contribution claim as a reusable Coq
entry point. A final delivery index now gathers the claim, writing, release,
status, artifact, and theorem handles into the current highest-level delivery
certificate. A complete entry point now compresses the final delivery index
into one top-level theorem. An automation daily-report certificate now gathers
the complete entry and the main report-facing handles for recurring status
updates. Direct daily-report route projections now expose the user-facing phase
order from unified syntax through MLTT, UTT, TDTT, translations, and
metatheory. A daily completion certificate now packages the report-facing route
and completion handles into one recurring automation endpoint. A daily-complete
entry point now compresses that certificate into one theorem for recurring
reports. A daily stage-route index now repackages the daily-complete route
handles into one directly citable stage certificate. A daily phase-route
consistency certificate now connects that daily route index with the global
phase-order certificate. Direct daily phase-route projection corollaries now
expose the major stage handles from that consistency certificate. A daily
final-route certificate now collects the report, completion, route consistency,
phase-order, stage-route, stage projection, metatheory, and artifact handles
into one final automation route endpoint. Direct daily final-route projection
corollaries now expose each of those handles from the final route certificate.
A daily automation final-entry index now gathers the daily-complete endpoint,
complete entry, final route, stage projection, metatheory, and artifact handles
into one top-level automation entry. Direct daily final-entry projection
corollaries now expose each major handle from that top-level entry. A daily
deliverable completion certificate now combines that final entry index with the
release summary, project status certificate, artifact index, route handles, and
stage projections.

## Release Summary

The current release-level theorem is
`type_theory_atlas_release_summary_holds`. It certifies that the Atlas
development has a verified paper-style statement, a completion index, a final
paper theorem, reusable system comparison and translation-reliability
summaries, a TDTT regularity dashboard, and a paper contribution summary. Its
`type_theory_atlas_release_gives_*` corollaries provide direct handles for each
release-level component.

## Artifact Index

The current artifact-level theorem is
`type_theory_atlas_artifact_index_holds`. It is the Coq-side index for the
release summary, project status certificate, paper-style statement, completion
index, final paper theorem, TDTT dashboard, and contribution summary. The build
checks below provide the external compilation and unfinished-proof-marker
evidence for this artifact state. Its `type_theory_atlas_artifact_gives_*`
corollaries provide direct handles for each artifact-level component.

## Phase Order Certificate

The theorem `type_theory_atlas_phase_order_certificate_holds` records the
automation route as a Coq certificate: unified syntax framework, MLTT, UTT,
TDTT, system translations, and final metatheory/artifact handles. Its
`type_theory_atlas_phase_order_gives_*` corollaries expose the artifact index,
unified syntax framework, MLTT/UTT/TDTT typing-support stages, system
embeddings, translation reliability summary, TDTT dashboard, and main theorem
directly.

## Paper Section Map

The theorem `type_theory_atlas_paper_section_map_holds` maps paper-facing
sections to verified Coq handles: introduction contribution, unified syntax,
MLTT, UTT, TDTT, translations, metatheory, and artifact index. Its
`type_theory_atlas_paper_section_gives_*` corollaries expose the main section
handles directly for writing and citation.

## Writing Checklist

The theorem `type_theory_atlas_writing_checklist_holds` gathers the
paper-section map, phase-order certificate, release summary, project status,
artifact index, paper statement, main/final theorem, completion index, and
contribution summary into one writing-facing Coq certificate. Its
`type_theory_atlas_writing_checklist_gives_*` corollaries expose each checklist
component directly.

## Paper Claim Index

The theorem `type_theory_atlas_paper_claim_index_holds` packages the final
paper-facing claim for "Type Theory Atlas in Coq": writing checklist, core
statement, unified framework, system comparison, translation reliability, TDTT
extension, metatheory, artifact index, release summary, and contribution
summary. Its `type_theory_atlas_paper_claim_gives_*` corollaries expose the
major claim components directly.

## Final Delivery Index

The theorem `type_theory_atlas_final_delivery_index_holds` is the current
highest-level delivery certificate. It gathers the paper-claim index, writing
checklist, section map, phase order, release summary, project status, artifact
index, paper statement, completion index, main/final theorem, final summary,
and contribution summary. Its `type_theory_atlas_final_delivery_gives_*`
corollaries expose the major delivery components directly.

## Complete Entry Point

The theorem `type_theory_atlas_complete` is the single top-level completion
entry point for the current artifact. It proves the final delivery index, and
its `type_theory_atlas_complete_gives_*` corollaries expose the paper-claim
index, artifact index, and main theorem directly.

## Automation Daily Report

The theorem `type_theory_atlas_automation_daily_report_holds` gathers the
complete entry, paper-claim index, artifact index, main theorem, phase order,
writing checklist, release summary, project status, final summary, and
contribution summary for recurring automation reports. Its
`type_theory_atlas_daily_report_gives_*` corollaries expose the main report
handles directly, including the route projections for unified syntax, MLTT,
UTT, TDTT, system embeddings, translation reliability, and metatheory.

## Daily Completion Certificate

The theorem `type_theory_atlas_daily_completion_certificate_holds` gathers the
daily report, complete entry, route projections, release summary, project
status, artifact index, final summary, and metatheory handles into one
recurring automation endpoint. Its `type_theory_atlas_daily_completion_gives_*`
corollaries expose the main completion and route components directly.

## Daily Complete Entry Point

The theorem `type_theory_atlas_daily_complete` is the single top-level theorem
for recurring automation reports. It proves the daily completion certificate,
and its `type_theory_atlas_daily_complete_gives_*` corollaries expose the daily
report, complete entry, route projections, artifact index, and metatheory
directly.

## Daily Stage Route Index

The theorem `type_theory_atlas_daily_stage_route_index_holds` packages the
daily-complete route projections into one certificate for the requested staged
route: unified syntax, MLTT, UTT, TDTT, system embeddings, translations, and
metatheory. The corollary
`type_theory_atlas_daily_complete_gives_stage_route_index` exposes that index
from the daily-complete entry point.

## Daily Phase Route Consistency

The theorem `type_theory_atlas_daily_phase_route_consistency_holds` connects
the daily stage-route index with the global phase-order certificate. It uses
`type_theory_atlas_daily_stage_route_index_from_phase_order` to rebuild the
daily route from the global phase-order route plus the daily-complete endpoint,
and `type_theory_atlas_daily_complete_gives_phase_route_consistency` exposes
the resulting consistency certificate from the daily entry point. Its
`type_theory_atlas_daily_phase_route_gives_*` corollaries expose the stage
route index, phase order, unified syntax, MLTT, UTT, TDTT, system embeddings,
translation reliability, metatheory, and artifact index directly.

## Daily Final Route Certificate

The theorem `type_theory_atlas_daily_final_route_certificate_holds` packages
the daily automation report, daily-complete endpoint, phase-route consistency,
stage-route index, phase order, unified syntax, MLTT, UTT, TDTT, system
embeddings, translation reliability, metatheory, and artifact index into one
final route certificate. The corollary
`type_theory_atlas_daily_complete_gives_final_route_certificate` exposes that
certificate from the daily-complete entry point. Its
`type_theory_atlas_daily_final_route_gives_*` corollaries expose the report,
daily-complete endpoint, phase consistency, stage-route index, phase order,
unified syntax, MLTT, UTT, TDTT, system embeddings, translation reliability,
metatheory, and artifact index directly.

## Daily Automation Final Entry Index

The theorem `type_theory_atlas_daily_automation_final_entry_index_holds`
packages the daily-complete endpoint, complete entry, final route certificate,
report, phase-route consistency, stage-route index, phase order, unified
syntax, MLTT, UTT, TDTT, system embeddings, translation reliability,
metatheory, and artifact index into one top-level automation entry. The
corollary `type_theory_atlas_daily_complete_gives_automation_final_entry_index`
exposes that index from the daily-complete entry point. Its
`type_theory_atlas_daily_final_entry_gives_*` corollaries expose completion,
report, final route, phase consistency, stage route, phase order, unified
syntax, MLTT, UTT, TDTT, system embeddings, translation reliability,
metatheory, and artifact index directly.

## Daily Deliverable Completion Certificate

The theorem `type_theory_atlas_daily_deliverable_completion_certificate_holds`
packages the final automation entry index, daily-complete endpoint, complete
entry, final route certificate, daily report, phase-route consistency,
stage-route index, phase order, release summary, project status certificate,
artifact index, unified syntax, MLTT, UTT, TDTT, system embeddings, translation
reliability, and metatheory into one report-facing completion certificate. The
corollary `type_theory_atlas_daily_complete_gives_deliverable_completion`
exposes that certificate from the daily-complete entry point. Its
`type_theory_atlas_daily_deliverable_gives_*` corollaries expose the final
entry index, completion handles, final route, daily report, phase route,
release summary, project status, artifact index, stage projections, and
metatheory directly. Its
`type_theory_atlas_daily_complete_gives_deliverable_*` corollaries expose the
same handles directly from the daily-complete entry point.

## Daily Report Facade

The theorem `type_theory_atlas_daily_report_facade_holds` packages the
daily-complete endpoint, deliverable completion certificate, final automation
entry index, complete entry, final route, daily report, phase-route
consistency, stage-route index, phase order, release summary, project status,
artifact index, unified syntax, MLTT, UTT, TDTT, system embeddings,
translation reliability, and metatheory into one facade for recurring
automation reports. The corollary
`type_theory_atlas_daily_complete_gives_report_facade` exposes that facade from
the daily-complete entry point. Its
`type_theory_atlas_daily_report_facade_gives_*` corollaries expose the entry
point, deliverable certificate, final entry index, complete entry, final route,
daily report, phase route, release summary, project status, artifact index,
stage projections, translations, and metatheory directly.

## Daily Release Certificate

The theorem `type_theory_atlas_daily_release_certificate_holds` packages the
daily report facade, stage-route index, phase-order certificate, final delivery
index, paper-claim index, paper-facing statement, and main theorem into one
release-level certificate for daily automation reports. The corollary
`type_theory_atlas_daily_report_facade_gives_release_certificate` exposes that
certificate from the daily report facade layer. Its
`type_theory_atlas_daily_release_gives_*` corollaries expose the facade, stage
route, phase order, final delivery, paper claim, paper statement, and main
theorem directly. The stage-specific corollaries
`type_theory_atlas_daily_release_gives_unified_syntax`,
`type_theory_atlas_daily_release_gives_mltt`,
`type_theory_atlas_daily_release_gives_utt`,
`type_theory_atlas_daily_release_gives_tdtt_typing`,
`type_theory_atlas_daily_release_gives_system_embeddings`,
`type_theory_atlas_daily_release_gives_translation`, and
`type_theory_atlas_daily_release_gives_metatheory` make the requested
six-stage route available from the release certificate itself.

The theorem `type_theory_atlas_daily_release_stage_consistency_holds` packages
the release certificate's stored stage-route index together with a stage-route
index rebuilt from its phase-order certificate. The corollary
`type_theory_atlas_daily_release_gives_stage_consistency` exposes this
consistency handle from the release layer, while its projections expose the
release certificate, stored stage route, phase-built stage route, and phase
order directly. Its stage projections
`type_theory_atlas_daily_release_stage_consistency_gives_unified_syntax`,
`type_theory_atlas_daily_release_stage_consistency_gives_mltt`,
`type_theory_atlas_daily_release_stage_consistency_gives_utt`,
`type_theory_atlas_daily_release_stage_consistency_gives_tdtt_typing`,
`type_theory_atlas_daily_release_stage_consistency_gives_tdtt_dashboard`,
`type_theory_atlas_daily_release_stage_consistency_gives_system_embeddings`,
`type_theory_atlas_daily_release_stage_consistency_gives_translation`, and
`type_theory_atlas_daily_release_stage_consistency_gives_metatheory` provide a
direct six-stage route from the consistency certificate.

## Daily Report Conclusion

The theorem `type_theory_atlas_daily_report_conclusion_holds` is the shortest
automation-facing conclusion for daily reports. It packages the daily release
certificate, release-stage consistency certificate, unified syntax, MLTT, UTT,
TDTT, TDTT dashboard, system embeddings, translation reliability, metatheory,
and paper-facing statement into one reusable endpoint. The corollary
`type_theory_atlas_daily_release_gives_report_conclusion` exposes this
conclusion from the release layer. Its
`type_theory_atlas_daily_report_conclusion_gives_*` corollaries expose the
release certificate, stage consistency, six-stage route, TDTT dashboard,
metatheory, and paper statement directly.

The theorem `type_theory_atlas_daily_conclusion_stage_order_summary_holds`
turns the conclusion into an explicit ordered route summary:
stage1 unified syntax, stage2 MLTT, stage3 UTT, stage4 TDTT, stage5 system
embeddings and translation reliability, and stage6 metatheory plus the
paper-facing statement. The corollary
`type_theory_atlas_daily_report_conclusion_gives_stage_order_summary` exposes
that ordered summary from the daily report conclusion.

## Daily Final Report Index

The theorem `type_theory_atlas_daily_final_report_index_holds` is the current
highest daily-report entry point. It packages the daily report conclusion, the
explicit stage-order summary, the daily release certificate, release-stage
consistency, metatheory, and the paper-facing statement into one final index.
The corollary `type_theory_atlas_daily_report_conclusion_gives_final_report_index`
exposes this final index from the daily report conclusion layer, while
`type_theory_atlas_daily_final_report_gives_*` projections expose its main
handles directly. Its stage projections expose stage1 unified syntax, stage2
MLTT, stage3 UTT, stage4 TDTT, stage5 system embeddings and translation
reliability, and stage6 metatheory plus the paper-facing statement directly
from the final index. The theorem
`type_theory_atlas_daily_final_stage_sync_certificate_holds` packages those
final stage projections together with the final report index as a Coq-level
sync certificate. The theorem
`type_theory_atlas_daily_automation_summary_certificate_holds` is the shortest
daily automation summary entry built from that final report and stage-sync
certificate, and its `type_theory_atlas_daily_automation_summary_gives_*`
corollaries expose the main summary handles directly. Its stage projections
also expose the full route from unified syntax through MLTT, UTT, TDTT,
translation, and metatheory. The theorem
`type_theory_atlas_daily_automation_stage_route_certificate_holds` packages
that summary-level route with the final stage-sync certificate, and its
`type_theory_atlas_daily_automation_stage_route_gives_*` corollaries expose the
route certificate handles directly. The theorem
`type_theory_atlas_daily_final_dashboard_certificate_holds` is the current final
daily dashboard entry for the automation, and its
`type_theory_atlas_daily_final_dashboard_gives_*` corollaries expose the
dashboard handles directly, including the full stage route from unified syntax
through MLTT, UTT, TDTT, translation, and metatheory. The theorem
`type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds`
packages that final dashboard route as a single certificate, and its
`type_theory_atlas_daily_final_dashboard_stage_route_gives_*` projections expose
the final route handles directly. The theorem
`type_theory_atlas_daily_final_dashboard_completion_certificate_holds` is the
current highest daily completion handle, and its
`type_theory_atlas_daily_final_dashboard_completion_gives_*` projections expose
the completion handles directly, including the full stage route from unified
syntax through MLTT, UTT, TDTT, translation, and metatheory.
`type_theory_atlas_paper_ready_completion_certificate_holds` packages that
completion handle into the current paper-ready completion certificate, and its
`type_theory_atlas_paper_ready_completion_gives_*` projections expose the
paper-ready evidence handles directly.
The theorem `type_theory_atlas_paper_ready_claim_index_holds` connects that
paper-ready completion certificate to the paper claim index and exposes the
claim-level proof handles directly through
`type_theory_atlas_paper_ready_claim_gives_*`.
The theorem `type_theory_atlas_paper_ready_abstract_certificate_holds` packages
the current abstract-level contribution route, and its
`type_theory_atlas_paper_ready_abstract_gives_*` projections expose the
abstract proof handles directly.
The theorem `type_theory_atlas_paper_ready_four_sentence_index_holds` packages
the paper abstract into four directly citable proof handles, and its
`type_theory_atlas_paper_ready_four_sentence_gives_*` projections expose those
handles directly.
The theorem `type_theory_atlas_paper_ready_abstract_final_certificate_holds`
packages those four handles and the paper-facing statement into the current
abstract-final certificate.
The theorem `type_theory_atlas_paper_ready_final_report_certificate_holds`
connects that abstract-final certificate with the current daily final dashboard
completion and final report index.
The theorem `type_theory_atlas_paper_ready_delivery_certificate_holds` connects
that final report certificate with the current release summary and project
status.
The theorem `type_theory_atlas_paper_ready_project_cover_certificate_holds`
packages that delivery certificate with the paper-facing statement, core
contribution summary, abstract-final route, release status, project status, and
validation dashboard.
The theorem `type_theory_atlas_paper_ready_automation_archive_certificate_holds`
packages the project-cover certificate with the daily automation summary and
final dashboard route for the current archive-level report.
The theorem `type_theory_atlas_paper_ready_automation_complete_certificate_holds`
packages the archive with the project cover, delivery certificate,
four-sentence index, daily completion, automation summary, final dashboard,
stage route, metatheory, and paper-facing statement.
The theorem `type_theory_atlas_public_entry_holds` is the short public entry
for that automation-complete certificate; its public projections recover the
daily completion, automation summary, final dashboard, stage route, system
embeddings, translation reliability, unified syntax, MLTT, UTT, TDTT typing,
TDTT dashboard, main theorem, and paper-facing statement.
The theorem `type_theory_atlas_public_route_certificate_holds` packages those
public route projections into one certificate, and
`type_theory_atlas_public_route_gives_*` exposes the same route fields for
direct reuse.
The theorem `type_theory_atlas_public_theorem_holds` is the shortest
paper-facing theorem alias for the completed public route, and its projections
expose the unified syntax, MLTT, UTT, TDTT, system-embedding,
translation-reliability, metatheory, and paper-facing components directly.
The theorem `type_theory_atlas_public_summary_certificate_holds` packages that
public theorem with the public route certificate, main theorem, and
paper-facing statement; its projections also recover the unified syntax,
MLTT, UTT, TDTT, system-embedding, and translation-reliability components.
The theorem `type_theory_atlas_public_delivery_certificate_holds` is the
current delivery-level certificate for the completed public route, and
`type_theory_atlas_public_delivery_gives_*` exposes its components directly.
The theorem `type_theory_atlas_public_final_certificate_holds` is the current
final public certificate for the completed automation route, and
`type_theory_atlas_public_final_gives_*` exposes its public and stage-route
components directly.
The theorem `type_theory_atlas_final_public_theorem_holds` is the single final
public theorem alias for the completed automation route, and its projections
recover the unified syntax, MLTT, UTT, TDTT, system-embedding,
translation-reliability, metatheory, and paper-facing components.
The theorem `type_theory_atlas_automation_done_holds` is the shortest
automation-complete entry for the project, and its projections recover the
same stage-route, metatheory, and paper-facing components as the final public
theorem.
The theorem `type_theory_atlas_automation_done_dashboard_certificate_holds`
packages that shortest entry with the current stage-route and report-facing
components, and `type_theory_atlas_automation_dashboard_gives_*` exposes those
dashboard fields directly.
The theorem `type_theory_atlas_daily_automation_report_complete_holds` is the
daily automation report-complete entry point, and its projections recover the
dashboard, final public theorem, stage-route, metatheory, and paper-facing
components from one report-ready handle.
The theorem `type_theory_atlas_public_release_manifest_holds` is the compact
public release manifest: it packages the daily report, dashboard, final public
theorem, final certificate, stage-route, metatheory, and paper-facing statement
into one citation-ready Coq handle.
The theorem `type_theory_atlas_public_release_complete_certificate_holds`
packages that citation-ready manifest with the final public theorem, final
certificate, daily report, dashboard, stage-route components, metatheory, and
paper-facing statement into one release-complete Coq handle.
The theorem `type_theory_atlas_public_release_complete_holds` is the shortest
final release entry point, and it recovers the release-complete certificate for
direct reuse. Its `type_theory_atlas_public_release_complete_entry_gives_*`
projections expose the stage route, translation reliability, metatheory, and
paper-facing statement from that short entry.
The theorem `type_theory_atlas_public_release_paper_route_certificate_holds`
packages that short final entry with the stage route, translation reliability,
main metatheory theorem, and paper-facing statement for paper-level citation.
The theorem `type_theory_atlas_public_release_paper_route_holds` is the
shortest paper-route theorem alias for that certificate.
Its `type_theory_atlas_public_release_paper_route_entry_gives_*` projections
expose the same stage route and paper-facing statement directly from the short
paper route entry.

## Homepage Summary

Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory.

Main contribution: this project formalizes a unified Coq framework for MLTT,
UTT, and TDTT, then compares their syntax, typing rules, translations, and
metatheory through reusable proof certificates.

Verified stage route: unified syntax framework -> MLTT -> UTT -> TDTT ->
system translations -> metatheory.

Final Coq entry point:
`type_theory_atlas_public_release_complete_holds`.

Paper route entry point:
`type_theory_atlas_public_release_paper_route_holds`.

Paper route certificate:
`type_theory_atlas_public_release_paper_route_certificate_holds`.

Release complete certificate:
`type_theory_atlas_public_release_complete_certificate_holds`.

Release manifest entry point:
`type_theory_atlas_public_release_manifest_holds`.

Verification entry point: `make check` runs the complete verification suite,
including README consistency checks, Coq clean rebuild, and unfinished-proof
scan.

## GitHub Homepage Snippet

Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory.

Core contribution: a unified Coq framework for MLTT, UTT, and TDTT, comparing
syntax, typing rules, translations, and metatheory through reusable proof
certificates.

Verified route: unified syntax framework -> MLTT -> UTT -> TDTT -> system translations -> metatheory.

Release manifest theorem: `type_theory_atlas_public_release_manifest_holds`.

Release complete certificate:
`type_theory_atlas_public_release_complete_certificate_holds`.

Shortest release entry:
`type_theory_atlas_public_release_complete_holds`.

Paper route certificate:
`type_theory_atlas_public_release_paper_route_certificate_holds`.

Paper route entry:
`type_theory_atlas_public_release_paper_route_holds`.

Release package check: `make check-public-release-final-package`.

Complete verification: `make check`.

Repository: https://github.com/yunbaoatxtu/type-theory-atlas-in-coq

## Public Release Citation

For a GitHub homepage, project README, or paper-facing summary, the verified
release entry can be cited as:

```text
Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory.
Repository: https://github.com/yunbaoatxtu/type-theory-atlas-in-coq
Coq release manifest: type_theory_atlas_public_release_manifest_holds
Coq release complete: type_theory_atlas_public_release_complete_holds
Coq paper route: type_theory_atlas_public_release_paper_route_holds
```

This citation points to the Coq-checked public release manifest, which packages
the unified syntax framework, MLTT, UTT, TDTT, system translations, metatheory,
and paper-facing statement into one release handle.

## Build Status Summary

The current public release complete entry point is
`type_theory_atlas_public_release_complete_holds`.
The current public release paper route entry point is
`type_theory_atlas_public_release_paper_route_holds`.
The current public release paper route certificate entry point is
`type_theory_atlas_public_release_paper_route_certificate_holds`.
The current public release manifest entry point is
`type_theory_atlas_public_release_manifest_holds`.
The current public release complete certificate entry point is
`type_theory_atlas_public_release_complete_certificate_holds`.
The current daily automation report-complete entry point is
`type_theory_atlas_daily_automation_report_complete_holds`.
The current automation-done dashboard entry point is
`type_theory_atlas_automation_done_dashboard_certificate_holds`.
The current automation-done entry point is `type_theory_atlas_automation_done_holds`.
The current final public theorem entry point is
`type_theory_atlas_final_public_theorem_holds`.
The current public final certificate entry point is
`type_theory_atlas_public_final_certificate_holds`.
The current public delivery certificate entry point is
`type_theory_atlas_public_delivery_certificate_holds`.
The current public summary certificate entry point is
`type_theory_atlas_public_summary_certificate_holds`.
The current public theorem entry point is `type_theory_atlas_public_theorem_holds`.
The current public route certificate entry point is
`type_theory_atlas_public_route_certificate_holds`.
The current public Atlas entry point is `type_theory_atlas_public_entry_holds`.
The current paper-ready automation complete entry point is
`type_theory_atlas_paper_ready_automation_complete_certificate_holds`.
The current paper-ready automation archive entry point is
`type_theory_atlas_paper_ready_automation_archive_certificate_holds`.
The current paper-ready project-cover entry point is
`type_theory_atlas_paper_ready_project_cover_certificate_holds`.
The current paper-ready delivery entry point is
`type_theory_atlas_paper_ready_delivery_certificate_holds`.
The current paper-ready final report entry point is
`type_theory_atlas_paper_ready_final_report_certificate_holds`.
The current paper-ready abstract-final entry point is
`type_theory_atlas_paper_ready_abstract_final_certificate_holds`.
The current paper-ready four-sentence entry point is
`type_theory_atlas_paper_ready_four_sentence_index_holds`.
The current paper-ready abstract entry point is
`type_theory_atlas_paper_ready_abstract_certificate_holds`.
The current paper-ready claim entry point is
`type_theory_atlas_paper_ready_claim_index_holds`.
The current paper-ready completion entry point is
`type_theory_atlas_paper_ready_completion_certificate_holds`.
The current daily automation entry point is
`type_theory_atlas_daily_final_dashboard_completion_certificate_holds`.
The current daily final dashboard is
`type_theory_atlas_daily_final_dashboard_certificate_holds`.
The current daily automation summary is
`type_theory_atlas_daily_automation_summary_certificate_holds`.
The current daily final report index is
`type_theory_atlas_daily_final_report_index_holds`.
The current daily report conclusion is
`type_theory_atlas_daily_report_conclusion_holds`.
The current daily release certificate is
`type_theory_atlas_daily_release_certificate_holds`.
The current daily report facade is `type_theory_atlas_daily_report_facade_holds`.
The foundational daily-complete theorem is `type_theory_atlas_daily_complete`.
The current artifact completion entry point is `type_theory_atlas_complete`.
The current paper-facing entry point is `type_theory_atlas_paper_statement_holds`.

The public release checklist is:

- release content package: `make check-public-release-final-package`;
- full daily verification: `make check`;
- clean Coq rebuild: `make clean && make -j1`;
- unfinished-proof scan: `make check-no-admits`;
- Coq release manifest theorem: `type_theory_atlas_public_release_manifest_holds`;
- Coq release complete theorem: `type_theory_atlas_public_release_complete_holds`;
- Coq release paper route theorem: `type_theory_atlas_public_release_paper_route_holds`;
- Coq release paper route certificate: `type_theory_atlas_public_release_paper_route_certificate_holds`;
- Coq release complete certificate: `type_theory_atlas_public_release_complete_certificate_holds`.

The expected verification story is:

- help for available targets: `make help`;
- full daily check: `make check`;
- full project build: `make clean && make -j1`;
- environment check: `make check-env`;
- README entry consistency check: `make check-readme-entries`;
- top-level entry sync check: `make check-daily-top-levels`;
- daily facade entry check: `make check-daily-facade`;
- daily facade projection check: `make check-daily-facade-projections`;
- stage-route projection check: `make check-stage-route`;
- daily release certificate check: `make check-daily-release`;
- daily report conclusion check: `make check-daily-conclusion`;
- daily final report index check: `make check-daily-final-report`;
- daily final stage-route check: `make check-daily-final-stage-route`;
- daily final stage-sync check: `make check-daily-final-stage-sync`;
- daily automation summary check: `make check-daily-automation-summary`;
- daily automation report-complete check: `make check-daily-automation-report-complete`;
- daily automation report stage-order check: `make check-daily-automation-report-stage-order`;
- daily automation report sync check: `make check-daily-automation-report-sync`;
- public release manifest check: `make check-public-release-manifest`;
- public release manifest stage-sync check: `make check-public-release-manifest-stage-sync`;
- public release complete certificate check: `make check-public-release-complete`;
- public release complete entry projection check: `make check-public-release-complete-entry-projections`;
- public release paper route entry check: `make check-public-release-paper-route-entry`;
- public release paper route check: `make check-public-release-paper-route`;
- public release paper route entry projection check: `make check-public-release-paper-route-entry-projections`;
- public homepage summary check: `make check-public-homepage-summary`;
- public homepage verification check: `make check-public-homepage-verification`;
- public GitHub homepage snippet check: `make check-public-github-homepage-snippet`;
- public GitHub repository sync check: `make check-public-github-repository-sync`;
- public release citation check: `make check-public-release-citation`;
- public release citation sync check: `make check-public-release-citation-sync`;
- public README release package check: `make check-public-readme-release-package`;
- public release final entry check: `make check-public-release-final-entry`;
- public README release map check: `make check-public-readme-release-map`;
- public release navigation check: `make check-public-release-navigation`;
- public release checklist check: `make check-public-release-checklist`;
- public source hygiene check: `make check-public-source-hygiene`;
- public release final package check: `make check-public-release-final-package`;
- expanded verification sync check: `make check-expanded-verification-sync`;
- help/README target sync check: `make check-help-readme-sync`;
- phony/help target sync check: `make check-phony-help-sync`;
- project file-order check: `make check-project-order`;
- unfinished-proof target: `make check-no-admits`;
- current Rocq environment: Rocq Prover 9.0.1;
- unfinished-proof scan:
  `rg -n "\b(Admitted|admit|Abort)\b" theories/Atlas -g "*.v"`;
- expected unfinished-proof scan result: no matches.

## Build

Install Coq (or a compatible Rocq distribution exposing `coqc` and
`coq_makefile`), then run:

```sh
make help
make check-env
make
```

For the current status certificate, the expected verification is:

```sh
make check
```

The expanded form is:

```sh
make check-env
make check-readme-entries
make check-daily-top-levels
make check-daily-facade
make check-daily-facade-projections
make check-stage-route
make check-daily-release
make check-daily-conclusion
make check-daily-final-report
make check-daily-final-stage-route
make check-daily-final-stage-sync
make check-daily-automation-summary
make check-daily-automation-report-complete
make check-daily-automation-report-stage-order
make check-daily-automation-report-sync
make check-public-release-final-package
make check-project-order
make clean && make -j1
make check-no-admits
rg -n "\b(Admitted|admit|Abort)\b" theories/Atlas -g "*.v"
```

The last command should produce no matches.

The build also detects Rocq Platform applications in `/Applications` and
mounted Rocq Platform installer images in `/Volumes`.
