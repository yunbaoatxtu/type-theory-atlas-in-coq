.PHONY: all clean help check check-env check-readme-entries check-daily-top-levels check-daily-facade check-daily-facade-projections check-stage-route check-daily-release check-daily-conclusion check-daily-final-report check-daily-final-stage-route check-daily-final-stage-sync check-daily-automation-summary check-daily-automation-report-complete check-daily-automation-report-stage-order check-daily-automation-report-sync check-public-release-manifest check-public-release-manifest-stage-sync check-public-release-complete check-public-homepage-summary check-public-homepage-verification check-public-github-homepage-snippet check-public-github-repository-sync check-public-release-citation check-public-release-citation-sync check-public-readme-release-package check-public-release-final-entry check-public-readme-release-map check-public-release-navigation check-public-release-checklist check-public-source-hygiene check-public-release-final-package check-expanded-verification-sync check-help-readme-sync check-phony-help-sync check-project-order check-no-admits

ROCQ_PLATFORM_RESOURCES := $(firstword \
	$(wildcard /Applications/Rocq-Platform~*.app/Contents/Resources) \
	$(wildcard /Applications/Coq-Platform~*.app/Contents/Resources) \
	$(wildcard /Volumes/Coq-*/Rocq-Platform~*.app/Contents/Resources) \
	$(wildcard /Volumes/Coq-*/Coq-Platform~*.app/Contents/Resources))

ifneq ($(ROCQ_PLATFORM_RESOURCES),)
export PATH := $(ROCQ_PLATFORM_RESOURCES)/bin:$(PATH)
export ROCQLIB ?= $(ROCQ_PLATFORM_RESOURCES)/lib/coq
export COQLIB ?= $(ROCQ_PLATFORM_RESOURCES)/lib/coq
PLATFORM_ENV := PATH="$(PATH)" ROCQLIB="$(ROCQLIB)" COQLIB="$(COQLIB)"
COQMAKEFILE ?= $(ROCQ_PLATFORM_RESOURCES)/bin/coq_makefile
COQC ?= $(ROCQ_PLATFORM_RESOURCES)/bin/coqc
else
COQMAKEFILE ?= coq_makefile
COQC ?= coqc
endif

all: Makefile.coq
	$(PLATFORM_ENV) $(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(PLATFORM_ENV) $(COQMAKEFILE) -f _CoqProject -o Makefile.coq

help:
	@echo "Type Theory Atlas in Coq"
	@echo ""
	@echo "Common targets:"
	@echo "  make              Build all Coq files"
	@echo "  make help         Show this help"
	@echo "  make check        Run the full daily verification"
	@echo "  make check-env    Show the detected Coq/Rocq compiler"
	@echo "  make check-readme-entries"
	@echo "                    Check README theorem names against Metatheory.v"
	@echo "  make check-daily-top-levels"
	@echo "                    Check README top-level and status entry names"
	@echo "  make check-daily-facade"
	@echo "                    Check README daily facade entry against Metatheory.v"
	@echo "  make check-daily-facade-projections"
	@echo "                    Check daily facade projection names"
	@echo "  make check-stage-route"
	@echo "                    Check phase-order and facade stage route names"
	@echo "  make check-daily-release"
	@echo "                    Check daily release certificate names"
	@echo "  make check-daily-conclusion"
	@echo "                    Check daily report conclusion names"
	@echo "  make check-daily-final-report"
	@echo "                    Check daily final report index names"
	@echo "  make check-daily-final-stage-route"
	@echo "                    Check daily final report stage route names"
	@echo "  make check-daily-final-stage-sync"
	@echo "                    Check final report stages mirror stage-order names"
	@echo "  make check-daily-automation-summary"
	@echo "                    Check daily automation summary names"
	@echo "  make check-daily-automation-report-complete"
	@echo "                    Check daily automation report-complete names"
	@echo "  make check-daily-automation-report-stage-order"
	@echo "                    Check daily automation report stage order"
	@echo "  make check-daily-automation-report-sync"
	@echo "                    Check daily automation report stage sync"
	@echo "  make check-public-release-manifest"
	@echo "                    Check public release manifest names"
	@echo "  make check-public-release-manifest-stage-sync"
	@echo "                    Check public release manifest stage order"
	@echo "  make check-public-release-complete"
	@echo "                    Check public release complete certificate"
	@echo "  make check-public-homepage-summary"
	@echo "                    Check public homepage summary snippet"
	@echo "  make check-public-homepage-verification"
	@echo "                    Check public homepage verification note"
	@echo "  make check-public-github-homepage-snippet"
	@echo "                    Check GitHub homepage snippet"
	@echo "  make check-public-github-repository-sync"
	@echo "                    Check GitHub repository references"
	@echo "  make check-public-release-citation"
	@echo "                    Check public release citation snippet"
	@echo "  make check-public-release-citation-sync"
	@echo "                    Check public release citation references"
	@echo "  make check-public-readme-release-package"
	@echo "                    Check public README release package"
	@echo "  make check-public-release-final-entry"
	@echo "                    Check final public release entry"
	@echo "  make check-public-readme-release-map"
	@echo "                    Check public README release map"
	@echo "  make check-public-release-navigation"
	@echo "                    Check public release README navigation"
	@echo "  make check-public-release-checklist"
	@echo "                    Check public release checklist"
	@echo "  make check-public-source-hygiene"
	@echo "                    Check tracked source hygiene"
	@echo "  make check-public-release-final-package"
	@echo "                    Check final public release package"
	@echo "  make check-expanded-verification-sync"
	@echo "                    Check README expanded verification order"
	@echo "  make check-help-readme-sync"
	@echo "                    Check help targets against README"
	@echo "  make check-phony-help-sync"
	@echo "                    Check .PHONY targets against help"
	@echo "  make check-project-order"
	@echo "                    Check _CoqProject file order against README layers"
	@echo "  make check-no-admits"
	@echo "                    Scan for Admitted, admit, or Abort"
	@echo "  make clean        Remove generated Coq build files"

check-env:
	@command -v $(COQC) >/dev/null || \
		(echo "Missing Coq compiler: install Coq or Rocq before building." && exit 1)
	@echo "Found Coq compiler: $$(command -v $(COQC))"
	@$(COQC) --version

check:
	$(MAKE) check-env
	$(MAKE) check-readme-entries
	$(MAKE) check-daily-top-levels
	$(MAKE) check-daily-facade
	$(MAKE) check-daily-facade-projections
	$(MAKE) check-stage-route
	$(MAKE) check-daily-release
	$(MAKE) check-daily-conclusion
	$(MAKE) check-daily-final-report
	$(MAKE) check-daily-final-stage-route
	$(MAKE) check-daily-final-stage-sync
	$(MAKE) check-daily-automation-summary
	$(MAKE) check-daily-automation-report-complete
	$(MAKE) check-daily-automation-report-stage-order
	$(MAKE) check-daily-automation-report-sync
	$(MAKE) check-public-release-final-package
	$(MAKE) check-project-order
	$(MAKE) clean
	$(MAKE) -j1 all
	$(MAKE) check-no-admits

check-readme-entries:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking README entries." && exit 1)
	@missing=0; \
	for entry in $$(sed -n '/^## Entry Consistency Checklist/,/^This project develops/p' README.md | grep -Eo '`[A-Za-z_][A-Za-z0-9_]*`' | tr -d '`' | sort -u); do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing README entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "README entry theorem names are present in theories/Atlas/Metatheory.v"

check-daily-top-levels:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking top-level entries." && exit 1)
	@missing=0; \
	for entry in \
		type_theory_atlas_public_release_complete_holds \
		type_theory_atlas_public_release_complete_certificate_holds \
		type_theory_atlas_public_release_manifest_holds \
		type_theory_atlas_daily_automation_report_complete_holds \
		type_theory_atlas_automation_done_dashboard_certificate_holds \
		type_theory_atlas_automation_done_holds \
		type_theory_atlas_final_public_theorem_holds \
		type_theory_atlas_public_final_certificate_holds \
		type_theory_atlas_public_delivery_certificate_holds \
		type_theory_atlas_public_summary_certificate_holds \
		type_theory_atlas_public_theorem_holds \
		type_theory_atlas_public_route_certificate_holds \
		type_theory_atlas_public_entry_holds \
		type_theory_atlas_paper_ready_automation_complete_certificate_holds \
		type_theory_atlas_paper_ready_automation_archive_certificate_holds \
		type_theory_atlas_paper_ready_project_cover_certificate_holds \
		type_theory_atlas_paper_ready_delivery_certificate_holds \
		type_theory_atlas_paper_ready_final_report_certificate_holds \
		type_theory_atlas_paper_ready_abstract_final_certificate_holds \
		type_theory_atlas_paper_ready_four_sentence_index_holds \
		type_theory_atlas_paper_ready_abstract_certificate_holds \
		type_theory_atlas_paper_ready_claim_index_holds \
		type_theory_atlas_paper_ready_completion_certificate_holds \
		type_theory_atlas_daily_final_dashboard_completion_certificate_holds \
		type_theory_atlas_daily_final_dashboard_certificate_holds \
		type_theory_atlas_daily_final_report_index_holds \
		type_theory_atlas_daily_automation_summary_certificate_holds \
		type_theory_atlas_daily_report_conclusion_holds \
		type_theory_atlas_daily_release_certificate_holds \
		type_theory_atlas_daily_report_facade_holds \
		type_theory_atlas_daily_complete \
		type_theory_atlas_complete \
		type_theory_atlas_paper_statement_holds; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing top-level entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q "$${entry}"; then \
			echo "Missing top-level entry in README.md: $$entry"; \
			missing=1; \
		fi; \
		if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q "$${entry}"; then \
			echo "Missing build-status top-level entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "README top-level entry names are synchronized across overview, build status, and Metatheory.v"

check-daily-facade:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily facade." && exit 1)
	@if ! rg -q '^Theorem type_theory_atlas_daily_report_facade_holds\b' theories/Atlas/Metatheory.v; then \
		echo "Missing daily facade theorem in theories/Atlas/Metatheory.v."; \
		exit 1; \
	fi
	@if ! rg -q '^- daily automation facade: `type_theory_atlas_daily_report_facade_holds`;' README.md; then \
		echo "README overview does not name the daily report facade."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q '`type_theory_atlas_daily_report_facade_holds`\.'; then \
		echo "README build status summary does not name the daily report facade."; \
		exit 1; \
	fi
	@echo "Daily automation facade entry is documented and present in Metatheory.v"

check-daily-facade-projections:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking facade projections." && exit 1)
	@missing=0; \
	for projection in \
		type_theory_atlas_daily_report_facade_gives_entry_point \
		type_theory_atlas_daily_report_facade_gives_deliverable_completion \
		type_theory_atlas_daily_report_facade_gives_final_entry_index \
		type_theory_atlas_daily_report_facade_gives_complete_entry \
		type_theory_atlas_daily_report_facade_gives_final_route \
		type_theory_atlas_daily_report_facade_gives_report \
		type_theory_atlas_daily_report_facade_gives_phase_consistency \
		type_theory_atlas_daily_report_facade_gives_stage_route_index \
		type_theory_atlas_daily_report_facade_gives_phase_order \
		type_theory_atlas_daily_report_facade_gives_release_summary \
		type_theory_atlas_daily_report_facade_gives_project_status \
		type_theory_atlas_daily_report_facade_gives_artifact_index \
		type_theory_atlas_daily_report_facade_gives_unified_syntax \
		type_theory_atlas_daily_report_facade_gives_mltt \
		type_theory_atlas_daily_report_facade_gives_utt \
		type_theory_atlas_daily_report_facade_gives_tdtt_typing \
		type_theory_atlas_daily_report_facade_gives_tdtt_dashboard \
		type_theory_atlas_daily_report_facade_gives_system_embeddings \
		type_theory_atlas_daily_report_facade_gives_translation \
		type_theory_atlas_daily_report_facade_gives_metatheory; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${projection}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily facade projection in theories/Atlas/Metatheory.v: $$projection"; \
			missing=1; \
		fi; \
		if ! rg -q "$${projection}" README.md; then \
			echo "Missing daily facade projection in README.md: $$projection"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily report facade projection names are documented and present in Metatheory.v"

check-stage-route:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the stage route." && exit 1)
	@missing=0; \
	for projection in \
		type_theory_atlas_phase_order_gives_unified_syntax_framework \
		type_theory_atlas_daily_report_facade_gives_unified_syntax \
		type_theory_atlas_phase_order_gives_mltt_typing_support \
		type_theory_atlas_daily_report_facade_gives_mltt \
		type_theory_atlas_phase_order_gives_utt_typing_support \
		type_theory_atlas_daily_report_facade_gives_utt \
		type_theory_atlas_phase_order_gives_tdtt_typing_support \
		type_theory_atlas_daily_report_facade_gives_tdtt_typing \
		type_theory_atlas_phase_order_gives_system_embeddings \
		type_theory_atlas_daily_report_facade_gives_system_embeddings \
		type_theory_atlas_phase_order_gives_translation_reliability \
		type_theory_atlas_daily_report_facade_gives_translation \
		type_theory_atlas_phase_order_gives_main_theorem \
		type_theory_atlas_daily_report_facade_gives_metatheory; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${projection}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing stage route projection in theories/Atlas/Metatheory.v: $$projection"; \
			missing=1; \
		fi; \
		if ! rg -q "$${projection}" README.md; then \
			echo "Missing stage route projection in README.md: $$projection"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Stage route projection names are documented and present in Metatheory.v"

check-daily-release:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily release certificate." && exit 1)
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_release_certificate \
		type_theory_atlas_daily_release_certificate_holds \
		type_theory_atlas_daily_report_facade_gives_release_certificate \
		type_theory_atlas_daily_release_gives_report_facade \
		type_theory_atlas_daily_release_gives_stage_route_index \
		type_theory_atlas_daily_release_gives_phase_order \
		type_theory_atlas_daily_release_gives_final_delivery_index \
		type_theory_atlas_daily_release_gives_paper_claim_index \
		type_theory_atlas_daily_release_gives_paper_statement \
		type_theory_atlas_daily_release_gives_main_theorem \
		type_theory_atlas_daily_release_gives_unified_syntax \
		type_theory_atlas_daily_release_gives_mltt \
		type_theory_atlas_daily_release_gives_utt \
		type_theory_atlas_daily_release_gives_tdtt_typing \
		type_theory_atlas_daily_release_gives_tdtt_dashboard \
		type_theory_atlas_daily_release_gives_system_embeddings \
		type_theory_atlas_daily_release_gives_translation \
		type_theory_atlas_daily_release_gives_metatheory \
		type_theory_atlas_daily_release_stage_consistency \
		type_theory_atlas_daily_release_stage_consistency_holds \
		type_theory_atlas_daily_release_gives_stage_consistency \
		type_theory_atlas_daily_release_stage_consistency_gives_release \
		type_theory_atlas_daily_release_stage_consistency_gives_stage_route \
		type_theory_atlas_daily_release_stage_consistency_gives_phase_built_route \
		type_theory_atlas_daily_release_stage_consistency_gives_phase_order \
		type_theory_atlas_daily_release_stage_consistency_gives_unified_syntax \
		type_theory_atlas_daily_release_stage_consistency_gives_mltt \
		type_theory_atlas_daily_release_stage_consistency_gives_utt \
		type_theory_atlas_daily_release_stage_consistency_gives_tdtt_typing \
		type_theory_atlas_daily_release_stage_consistency_gives_tdtt_dashboard \
		type_theory_atlas_daily_release_stage_consistency_gives_system_embeddings \
		type_theory_atlas_daily_release_stage_consistency_gives_translation \
		type_theory_atlas_daily_release_stage_consistency_gives_metatheory; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily release entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily release entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily release certificate names are documented and present in Metatheory.v"

check-daily-conclusion:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily report conclusion." && exit 1)
	@if ! rg -q '^- daily report conclusion:' README.md; then \
		echo "README overview does not name the daily report conclusion."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q '`type_theory_atlas_daily_report_conclusion_holds`\.'; then \
		echo "README build status summary does not name the daily report conclusion."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_report_conclusion \
		type_theory_atlas_daily_report_conclusion_holds \
		type_theory_atlas_daily_release_gives_report_conclusion \
		type_theory_atlas_daily_report_conclusion_gives_release_certificate \
		type_theory_atlas_daily_report_conclusion_gives_stage_consistency \
		type_theory_atlas_daily_report_conclusion_gives_unified_syntax \
		type_theory_atlas_daily_report_conclusion_gives_mltt \
		type_theory_atlas_daily_report_conclusion_gives_utt \
		type_theory_atlas_daily_report_conclusion_gives_tdtt_typing \
		type_theory_atlas_daily_report_conclusion_gives_tdtt_dashboard \
		type_theory_atlas_daily_report_conclusion_gives_system_embeddings \
		type_theory_atlas_daily_report_conclusion_gives_translation \
		type_theory_atlas_daily_report_conclusion_gives_metatheory \
		type_theory_atlas_daily_report_conclusion_gives_paper_statement \
		type_theory_atlas_daily_conclusion_stage_order_summary \
		type_theory_atlas_daily_conclusion_stage_order_summary_holds \
		type_theory_atlas_daily_report_conclusion_gives_stage_order_summary \
		type_theory_atlas_daily_conclusion_stage_order_gives_conclusion \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage1_unified_syntax \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage2_mltt \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage3_utt \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage5_system_embeddings \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage5_translation \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage6_metatheory \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage6_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily conclusion entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily conclusion entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily report conclusion names are documented and present in Metatheory.v"

check-daily-final-report:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily final report index." && exit 1)
	@if ! rg -q '^- daily final report index:' README.md; then \
		echo "README overview does not name the daily final report index."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q '`type_theory_atlas_daily_final_report_index_holds`\.'; then \
		echo "README build status summary does not name the daily final report index."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_final_report_index \
		type_theory_atlas_daily_final_report_index_holds \
		type_theory_atlas_daily_report_conclusion_gives_final_report_index \
		type_theory_atlas_daily_final_report_gives_conclusion \
		type_theory_atlas_daily_final_report_gives_stage_order_summary \
		type_theory_atlas_daily_final_report_gives_release_certificate \
		type_theory_atlas_daily_final_report_gives_stage_consistency \
		type_theory_atlas_daily_final_report_gives_metatheory \
		type_theory_atlas_daily_final_report_gives_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily final report entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily final report entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily final report index names are documented and present in Metatheory.v"

check-daily-final-stage-route:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily final stage route." && exit 1)
	@if ! rg -q '^- Daily final report stage projections:' README.md; then \
		echo "README entry checklist does not name the daily final report stage projections."; \
		exit 1; \
	fi
	@if ! rg -q 'daily final stage-route check: `make check-daily-final-stage-route`' README.md; then \
		echo "README build status summary does not name the daily final stage route check."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_final_report_gives_stage1_unified_syntax \
		type_theory_atlas_daily_final_report_gives_stage2_mltt \
		type_theory_atlas_daily_final_report_gives_stage3_utt \
		type_theory_atlas_daily_final_report_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_final_report_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_final_report_gives_stage5_system_embeddings \
		type_theory_atlas_daily_final_report_gives_stage5_translation \
		type_theory_atlas_daily_final_report_gives_stage6_metatheory \
		type_theory_atlas_daily_final_report_gives_stage6_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily final stage route entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily final stage route entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily final report stage route names are documented and present in Metatheory.v"

check-daily-final-stage-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking final stage synchronization." && exit 1)
	@if ! rg -q 'daily final stage-sync check: `make check-daily-final-stage-sync`' README.md; then \
		echo "README build status summary does not name the daily final stage sync check."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_final_stage_sync_certificate \
		type_theory_atlas_daily_final_stage_sync_certificate_holds \
		type_theory_atlas_daily_final_report_gives_stage_sync_certificate; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily final stage-sync certificate in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily final stage-sync certificate in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi
	@expected_conclusion=$$(mktemp); actual_conclusion=$$(mktemp); \
	expected_final=$$(mktemp); actual_final=$$(mktemp); \
	printf '%s\n' \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage1_unified_syntax \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage2_mltt \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage3_utt \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage5_system_embeddings \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage5_translation \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage6_metatheory \
		type_theory_atlas_daily_conclusion_stage_order_gives_stage6_paper_statement > "$$expected_conclusion"; \
	printf '%s\n' \
		type_theory_atlas_daily_final_report_gives_stage1_unified_syntax \
		type_theory_atlas_daily_final_report_gives_stage2_mltt \
		type_theory_atlas_daily_final_report_gives_stage3_utt \
		type_theory_atlas_daily_final_report_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_final_report_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_final_report_gives_stage5_system_embeddings \
		type_theory_atlas_daily_final_report_gives_stage5_translation \
		type_theory_atlas_daily_final_report_gives_stage6_metatheory \
		type_theory_atlas_daily_final_report_gives_stage6_paper_statement > "$$expected_final"; \
	sed -n '/^- Daily conclusion stage-order projections:/,/^- Daily final report index:/p' README.md | \
		grep -Eo '`type_theory_atlas_daily_conclusion_stage_order_gives_stage[0-9][A-Za-z0-9_]*`' | \
		tr -d '`' > "$$actual_conclusion"; \
	sed -n '/^- Daily final report stage projections:/,/^- Build status checks:/p' README.md | \
		grep -Eo '`type_theory_atlas_daily_final_report_gives_stage[0-9][A-Za-z0-9_]*`' | \
		tr -d '`' > "$$actual_final"; \
	missing=0; \
	if ! diff -u "$$expected_conclusion" "$$actual_conclusion"; then \
		echo "README daily conclusion stage-order projections are not in the expected order."; \
		missing=1; \
	fi; \
	if ! diff -u "$$expected_final" "$$actual_final"; then \
		echo "README daily final report stage projections are not in the expected order."; \
		missing=1; \
	fi; \
	for suffix in \
		stage1_unified_syntax \
		stage2_mltt \
		stage3_utt \
		stage4_tdtt_typing \
		stage4_tdtt_dashboard \
		stage5_system_embeddings \
		stage5_translation \
		stage6_metatheory \
		stage6_paper_statement; do \
		for entry in \
			type_theory_atlas_daily_conclusion_stage_order_gives_$${suffix} \
			type_theory_atlas_daily_final_report_gives_$${suffix}; do \
			if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
				echo "Missing synchronized stage projection in theories/Atlas/Metatheory.v: $$entry"; \
				missing=1; \
			fi; \
		done; \
	done; \
	rm -f "$$expected_conclusion" "$$actual_conclusion" "$$expected_final" "$$actual_final"; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily final report stage projections mirror the conclusion stage-order projections."

check-daily-automation-summary:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily automation summary." && exit 1)
	@if ! rg -q 'daily automation summary check: `make check-daily-automation-summary`' README.md; then \
		echo "README build status summary does not name the daily automation summary check."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_automation_summary_certificate \
		type_theory_atlas_daily_automation_summary_certificate_holds \
		type_theory_atlas_daily_final_report_gives_automation_summary_certificate \
		type_theory_atlas_daily_automation_summary_gives_final_report \
		type_theory_atlas_daily_automation_summary_gives_stage_sync \
		type_theory_atlas_daily_automation_summary_gives_conclusion \
		type_theory_atlas_daily_automation_summary_gives_release_certificate \
		type_theory_atlas_daily_automation_summary_gives_facade \
		type_theory_atlas_daily_automation_summary_gives_daily_complete \
		type_theory_atlas_daily_automation_summary_gives_artifact_complete \
		type_theory_atlas_daily_automation_summary_gives_release_summary \
		type_theory_atlas_daily_automation_summary_gives_project_status \
		type_theory_atlas_daily_automation_summary_gives_metatheory \
		type_theory_atlas_daily_automation_summary_gives_paper_statement \
		type_theory_atlas_daily_automation_summary_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_summary_gives_stage2_mltt \
		type_theory_atlas_daily_automation_summary_gives_stage3_utt \
		type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_summary_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_summary_gives_stage5_translation \
		type_theory_atlas_daily_automation_summary_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_summary_gives_stage6_paper_statement \
		type_theory_atlas_daily_automation_stage_route_certificate \
		type_theory_atlas_daily_automation_stage_route_certificate_holds \
		type_theory_atlas_daily_automation_summary_gives_stage_route_certificate \
		type_theory_atlas_daily_automation_stage_route_gives_summary \
		type_theory_atlas_daily_automation_stage_route_gives_stage_sync \
		type_theory_atlas_daily_automation_stage_route_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_stage_route_gives_stage2_mltt \
		type_theory_atlas_daily_automation_stage_route_gives_stage3_utt \
		type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_stage_route_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_stage_route_gives_stage5_translation \
		type_theory_atlas_daily_automation_stage_route_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_stage_route_gives_stage6_paper_statement \
		type_theory_atlas_daily_final_dashboard_certificate \
		type_theory_atlas_daily_final_dashboard_certificate_holds \
		type_theory_atlas_daily_automation_summary_gives_final_dashboard \
		type_theory_atlas_daily_final_dashboard_gives_automation_summary \
		type_theory_atlas_daily_final_dashboard_gives_stage_route \
		type_theory_atlas_daily_final_dashboard_gives_final_report \
		type_theory_atlas_daily_final_dashboard_gives_stage_sync \
		type_theory_atlas_daily_final_dashboard_gives_release_summary \
		type_theory_atlas_daily_final_dashboard_gives_project_status \
		type_theory_atlas_daily_final_dashboard_gives_metatheory \
		type_theory_atlas_daily_final_dashboard_gives_paper_statement \
		type_theory_atlas_daily_final_dashboard_gives_stage1_unified_syntax \
		type_theory_atlas_daily_final_dashboard_gives_stage2_mltt \
		type_theory_atlas_daily_final_dashboard_gives_stage3_utt \
		type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_final_dashboard_gives_stage5_system_embeddings \
		type_theory_atlas_daily_final_dashboard_gives_stage5_translation \
		type_theory_atlas_daily_final_dashboard_gives_stage6_metatheory \
		type_theory_atlas_daily_final_dashboard_gives_stage6_paper_statement \
		type_theory_atlas_daily_final_dashboard_stage_route_certificate \
		type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds \
		type_theory_atlas_daily_final_dashboard_gives_stage_route_certificate \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_dashboard \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_route \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage1_unified_syntax \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage2_mltt \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage3_utt \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_system_embeddings \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_translation \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_metatheory \
		type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_paper_statement \
		type_theory_atlas_daily_final_dashboard_completion_certificate \
		type_theory_atlas_daily_final_dashboard_completion_certificate_holds \
		type_theory_atlas_daily_final_dashboard_gives_completion_certificate \
		type_theory_atlas_daily_final_dashboard_completion_gives_dashboard \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage_route \
		type_theory_atlas_daily_final_dashboard_completion_gives_automation_summary \
		type_theory_atlas_daily_final_dashboard_completion_gives_final_report \
		type_theory_atlas_daily_final_dashboard_completion_gives_release_summary \
		type_theory_atlas_daily_final_dashboard_completion_gives_project_status \
		type_theory_atlas_daily_final_dashboard_completion_gives_metatheory \
		type_theory_atlas_daily_final_dashboard_completion_gives_paper_statement \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage1_unified_syntax \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage2_mltt \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage3_utt \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage5_system_embeddings \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage5_translation \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage6_metatheory \
		type_theory_atlas_daily_final_dashboard_completion_gives_stage6_paper_statement \
		type_theory_atlas_paper_ready_completion_certificate \
		type_theory_atlas_paper_ready_completion_certificate_holds \
		type_theory_atlas_daily_final_dashboard_completion_gives_paper_ready_certificate \
		type_theory_atlas_paper_ready_completion_gives_completion_handle \
		type_theory_atlas_paper_ready_completion_gives_dashboard \
		type_theory_atlas_paper_ready_completion_gives_stage_route \
		type_theory_atlas_paper_ready_completion_gives_unified_syntax \
		type_theory_atlas_paper_ready_completion_gives_mltt \
		type_theory_atlas_paper_ready_completion_gives_utt \
		type_theory_atlas_paper_ready_completion_gives_tdtt_typing \
		type_theory_atlas_paper_ready_completion_gives_tdtt_dashboard \
		type_theory_atlas_paper_ready_completion_gives_system_embeddings \
		type_theory_atlas_paper_ready_completion_gives_translation \
		type_theory_atlas_paper_ready_completion_gives_metatheory \
		type_theory_atlas_paper_ready_completion_gives_paper_statement \
		type_theory_atlas_paper_ready_claim_index \
		type_theory_atlas_paper_ready_claim_index_holds \
		type_theory_atlas_paper_ready_completion_gives_claim_index \
		type_theory_atlas_paper_ready_claim_gives_completion \
		type_theory_atlas_paper_ready_claim_gives_claim_index \
		type_theory_atlas_paper_ready_claim_gives_statement \
		type_theory_atlas_paper_ready_claim_gives_final_paper_theorem \
		type_theory_atlas_paper_ready_claim_gives_contribution_summary \
		type_theory_atlas_paper_ready_claim_gives_system_comparison \
		type_theory_atlas_paper_ready_claim_gives_translation \
		type_theory_atlas_paper_ready_claim_gives_tdtt \
		type_theory_atlas_paper_ready_claim_gives_metatheory \
		type_theory_atlas_paper_ready_abstract_certificate \
		type_theory_atlas_paper_ready_abstract_certificate_holds \
		type_theory_atlas_paper_ready_claim_gives_abstract_certificate \
		type_theory_atlas_paper_ready_abstract_gives_claim_index \
		type_theory_atlas_paper_ready_abstract_gives_completion \
		type_theory_atlas_paper_ready_abstract_gives_unified_framework \
		type_theory_atlas_paper_ready_abstract_gives_mltt \
		type_theory_atlas_paper_ready_abstract_gives_utt \
		type_theory_atlas_paper_ready_abstract_gives_tdtt_typing \
		type_theory_atlas_paper_ready_abstract_gives_tdtt_dashboard \
		type_theory_atlas_paper_ready_abstract_gives_translation \
		type_theory_atlas_paper_ready_abstract_gives_metatheory \
		type_theory_atlas_paper_ready_abstract_gives_paper_statement \
		type_theory_atlas_paper_ready_four_sentence_index \
		type_theory_atlas_paper_ready_four_sentence_index_holds \
		type_theory_atlas_paper_ready_abstract_gives_four_sentence_index \
		type_theory_atlas_paper_ready_four_sentence_gives_unified_framework \
		type_theory_atlas_paper_ready_four_sentence_gives_three_systems \
		type_theory_atlas_paper_ready_four_sentence_gives_translations \
		type_theory_atlas_paper_ready_four_sentence_gives_metatheory \
		type_theory_atlas_paper_ready_four_sentence_gives_paper_statement \
		type_theory_atlas_paper_ready_abstract_sentence_1_unified_framework \
		type_theory_atlas_paper_ready_abstract_sentence_2_three_systems \
		type_theory_atlas_paper_ready_abstract_sentence_3_translations \
		type_theory_atlas_paper_ready_abstract_sentence_4_metatheory \
		type_theory_atlas_paper_ready_abstract_final_certificate \
		type_theory_atlas_paper_ready_abstract_final_certificate_holds \
		type_theory_atlas_paper_ready_four_sentence_gives_abstract_final_certificate \
		type_theory_atlas_paper_ready_abstract_final_gives_four_sentence_index \
		type_theory_atlas_paper_ready_abstract_final_gives_sentence_1 \
		type_theory_atlas_paper_ready_abstract_final_gives_sentence_2 \
		type_theory_atlas_paper_ready_abstract_final_gives_sentence_3 \
		type_theory_atlas_paper_ready_abstract_final_gives_sentence_4 \
		type_theory_atlas_paper_ready_abstract_final_gives_paper_statement \
		type_theory_atlas_paper_ready_final_report_certificate \
		type_theory_atlas_paper_ready_final_report_certificate_holds \
		type_theory_atlas_paper_ready_abstract_final_gives_final_report_certificate \
		type_theory_atlas_paper_ready_final_report_gives_abstract_final \
		type_theory_atlas_paper_ready_final_report_gives_daily_completion \
		type_theory_atlas_paper_ready_final_report_gives_daily_report \
		type_theory_atlas_paper_ready_final_report_gives_dashboard \
		type_theory_atlas_paper_ready_final_report_gives_stage_route \
		type_theory_atlas_paper_ready_final_report_gives_four_sentence_index \
		type_theory_atlas_paper_ready_final_report_gives_metatheory \
		type_theory_atlas_paper_ready_final_report_gives_paper_statement \
		type_theory_atlas_paper_ready_delivery_certificate \
		type_theory_atlas_paper_ready_delivery_certificate_holds \
		type_theory_atlas_paper_ready_final_report_gives_delivery_certificate \
		type_theory_atlas_paper_ready_delivery_gives_final_report \
		type_theory_atlas_paper_ready_delivery_gives_daily_completion \
		type_theory_atlas_paper_ready_delivery_gives_release_summary \
		type_theory_atlas_paper_ready_delivery_gives_project_status \
		type_theory_atlas_paper_ready_delivery_gives_dashboard \
		type_theory_atlas_paper_ready_delivery_gives_abstract_final \
		type_theory_atlas_paper_ready_delivery_gives_four_sentence_index \
		type_theory_atlas_paper_ready_delivery_gives_metatheory \
		type_theory_atlas_paper_ready_delivery_gives_paper_statement \
		type_theory_atlas_paper_ready_project_cover_certificate \
		type_theory_atlas_paper_ready_project_cover_certificate_holds \
		type_theory_atlas_paper_ready_delivery_gives_project_cover_certificate \
		type_theory_atlas_paper_ready_project_cover_gives_delivery \
		type_theory_atlas_paper_ready_project_cover_gives_paper_statement \
		type_theory_atlas_paper_ready_project_cover_gives_core_contribution \
		type_theory_atlas_paper_ready_project_cover_gives_abstract_final \
		type_theory_atlas_paper_ready_project_cover_gives_four_sentence_index \
		type_theory_atlas_paper_ready_project_cover_gives_release_summary \
		type_theory_atlas_paper_ready_project_cover_gives_project_status \
		type_theory_atlas_paper_ready_project_cover_gives_daily_completion \
		type_theory_atlas_paper_ready_project_cover_gives_validation_dashboard \
		type_theory_atlas_paper_ready_project_cover_gives_metatheory \
		type_theory_atlas_paper_ready_automation_archive_certificate \
		type_theory_atlas_paper_ready_automation_archive_certificate_holds \
		type_theory_atlas_paper_ready_project_cover_gives_automation_archive_certificate \
		type_theory_atlas_paper_ready_archive_gives_project_cover \
		type_theory_atlas_paper_ready_archive_gives_delivery \
		type_theory_atlas_paper_ready_archive_gives_daily_completion \
		type_theory_atlas_paper_ready_archive_gives_automation_summary \
		type_theory_atlas_paper_ready_archive_gives_final_dashboard \
		type_theory_atlas_paper_ready_archive_gives_release_summary \
		type_theory_atlas_paper_ready_archive_gives_project_status \
		type_theory_atlas_paper_ready_archive_gives_stage_route \
		type_theory_atlas_paper_ready_archive_gives_metatheory \
		type_theory_atlas_paper_ready_archive_gives_paper_statement \
		type_theory_atlas_paper_ready_automation_complete_certificate \
		type_theory_atlas_paper_ready_automation_complete_certificate_holds \
		type_theory_atlas_paper_ready_archive_gives_automation_complete_certificate \
		type_theory_atlas_paper_ready_complete_gives_archive \
		type_theory_atlas_paper_ready_complete_gives_project_cover \
		type_theory_atlas_paper_ready_complete_gives_delivery \
		type_theory_atlas_paper_ready_complete_gives_four_sentence_index \
		type_theory_atlas_paper_ready_complete_gives_daily_completion \
		type_theory_atlas_paper_ready_complete_gives_automation_summary \
		type_theory_atlas_paper_ready_complete_gives_final_dashboard \
		type_theory_atlas_paper_ready_complete_gives_stage_route \
		type_theory_atlas_paper_ready_complete_gives_metatheory \
		type_theory_atlas_paper_ready_complete_gives_paper_statement \
		type_theory_atlas_public_entry \
		type_theory_atlas_public_entry_holds \
		type_theory_atlas_public_entry_gives_paper_ready_complete \
		type_theory_atlas_public_entry_gives_daily_completion \
		type_theory_atlas_public_entry_gives_automation_summary \
		type_theory_atlas_public_entry_gives_final_dashboard \
		type_theory_atlas_public_entry_gives_stage_route \
		type_theory_atlas_public_entry_gives_unified_syntax \
		type_theory_atlas_public_entry_gives_mltt \
		type_theory_atlas_public_entry_gives_utt \
		type_theory_atlas_public_entry_gives_tdtt_typing \
		type_theory_atlas_public_entry_gives_tdtt_dashboard \
		type_theory_atlas_public_entry_gives_system_embeddings \
		type_theory_atlas_public_entry_gives_translation_reliability \
		type_theory_atlas_public_entry_gives_main_theorem \
		type_theory_atlas_public_entry_gives_paper_statement \
		type_theory_atlas_public_route_certificate \
		type_theory_atlas_public_route_certificate_holds \
		type_theory_atlas_public_entry_gives_route_certificate \
		type_theory_atlas_public_route_gives_entry \
		type_theory_atlas_public_route_gives_unified_syntax \
		type_theory_atlas_public_route_gives_mltt \
		type_theory_atlas_public_route_gives_utt \
		type_theory_atlas_public_route_gives_tdtt_typing \
		type_theory_atlas_public_route_gives_tdtt_dashboard \
		type_theory_atlas_public_route_gives_system_embeddings \
		type_theory_atlas_public_route_gives_translation_reliability \
		type_theory_atlas_public_route_gives_main_theorem \
		type_theory_atlas_public_route_gives_paper_statement \
		type_theory_atlas_public_theorem \
		type_theory_atlas_public_theorem_holds \
		type_theory_atlas_public_theorem_gives_route_certificate \
		type_theory_atlas_public_theorem_gives_unified_syntax \
		type_theory_atlas_public_theorem_gives_mltt \
		type_theory_atlas_public_theorem_gives_utt \
		type_theory_atlas_public_theorem_gives_tdtt_typing \
		type_theory_atlas_public_theorem_gives_tdtt_dashboard \
		type_theory_atlas_public_theorem_gives_system_embeddings \
		type_theory_atlas_public_theorem_gives_translation_reliability \
		type_theory_atlas_public_theorem_gives_main_theorem \
		type_theory_atlas_public_theorem_gives_paper_statement \
		type_theory_atlas_public_summary_certificate \
		type_theory_atlas_public_summary_certificate_holds \
		type_theory_atlas_public_theorem_gives_summary_certificate \
		type_theory_atlas_public_summary_gives_public_theorem \
		type_theory_atlas_public_summary_gives_route_certificate \
		type_theory_atlas_public_summary_gives_unified_syntax \
		type_theory_atlas_public_summary_gives_mltt \
		type_theory_atlas_public_summary_gives_utt \
		type_theory_atlas_public_summary_gives_tdtt_typing \
		type_theory_atlas_public_summary_gives_tdtt_dashboard \
		type_theory_atlas_public_summary_gives_system_embeddings \
		type_theory_atlas_public_summary_gives_translation_reliability \
		type_theory_atlas_public_summary_gives_main_theorem \
		type_theory_atlas_public_summary_gives_paper_statement \
		type_theory_atlas_public_delivery_certificate \
		type_theory_atlas_public_delivery_certificate_holds \
		type_theory_atlas_public_summary_gives_delivery_certificate \
		type_theory_atlas_public_delivery_gives_summary \
		type_theory_atlas_public_delivery_gives_public_theorem \
		type_theory_atlas_public_delivery_gives_route_certificate \
		type_theory_atlas_public_delivery_gives_unified_syntax \
		type_theory_atlas_public_delivery_gives_mltt \
		type_theory_atlas_public_delivery_gives_utt \
		type_theory_atlas_public_delivery_gives_tdtt_typing \
		type_theory_atlas_public_delivery_gives_tdtt_dashboard \
		type_theory_atlas_public_delivery_gives_system_embeddings \
		type_theory_atlas_public_delivery_gives_translation_reliability \
		type_theory_atlas_public_delivery_gives_main_theorem \
		type_theory_atlas_public_delivery_gives_paper_statement \
		type_theory_atlas_public_final_certificate \
		type_theory_atlas_public_final_certificate_holds \
		type_theory_atlas_public_delivery_gives_final_certificate \
		type_theory_atlas_public_final_gives_delivery \
		type_theory_atlas_public_final_gives_summary \
		type_theory_atlas_public_final_gives_public_theorem \
		type_theory_atlas_public_final_gives_route_certificate \
		type_theory_atlas_public_final_gives_entry \
		type_theory_atlas_public_final_gives_unified_syntax \
		type_theory_atlas_public_final_gives_mltt \
		type_theory_atlas_public_final_gives_utt \
		type_theory_atlas_public_final_gives_tdtt_typing \
		type_theory_atlas_public_final_gives_tdtt_dashboard \
		type_theory_atlas_public_final_gives_system_embeddings \
		type_theory_atlas_public_final_gives_translation_reliability \
		type_theory_atlas_public_final_gives_main_theorem \
		type_theory_atlas_public_final_gives_paper_statement \
		type_theory_atlas_final_public_theorem \
		type_theory_atlas_final_public_theorem_holds \
		type_theory_atlas_final_public_theorem_gives_final_certificate \
		type_theory_atlas_final_public_theorem_gives_unified_syntax \
		type_theory_atlas_final_public_theorem_gives_mltt \
		type_theory_atlas_final_public_theorem_gives_utt \
		type_theory_atlas_final_public_theorem_gives_tdtt_typing \
		type_theory_atlas_final_public_theorem_gives_tdtt_dashboard \
		type_theory_atlas_final_public_theorem_gives_system_embeddings \
		type_theory_atlas_final_public_theorem_gives_translation_reliability \
		type_theory_atlas_final_public_theorem_gives_main_theorem \
		type_theory_atlas_final_public_theorem_gives_paper_statement \
		type_theory_atlas_automation_done \
		type_theory_atlas_automation_done_holds \
		type_theory_atlas_automation_done_gives_final_public_theorem \
		type_theory_atlas_automation_done_gives_unified_syntax \
		type_theory_atlas_automation_done_gives_mltt \
		type_theory_atlas_automation_done_gives_utt \
		type_theory_atlas_automation_done_gives_tdtt_typing \
		type_theory_atlas_automation_done_gives_tdtt_dashboard \
		type_theory_atlas_automation_done_gives_system_embeddings \
		type_theory_atlas_automation_done_gives_translation_reliability \
		type_theory_atlas_automation_done_gives_main_theorem \
		type_theory_atlas_automation_done_gives_paper_statement \
		type_theory_atlas_automation_done_dashboard_certificate \
		type_theory_atlas_automation_done_dashboard_certificate_holds \
		type_theory_atlas_automation_done_gives_dashboard_certificate \
		type_theory_atlas_automation_dashboard_gives_done \
		type_theory_atlas_automation_dashboard_gives_final_public_theorem \
		type_theory_atlas_automation_dashboard_gives_unified_syntax \
		type_theory_atlas_automation_dashboard_gives_mltt \
		type_theory_atlas_automation_dashboard_gives_utt \
		type_theory_atlas_automation_dashboard_gives_tdtt_typing \
		type_theory_atlas_automation_dashboard_gives_tdtt_dashboard \
		type_theory_atlas_automation_dashboard_gives_system_embeddings \
		type_theory_atlas_automation_dashboard_gives_translation_reliability \
		type_theory_atlas_automation_dashboard_gives_main_theorem \
		type_theory_atlas_automation_dashboard_gives_paper_statement \
		type_theory_atlas_daily_automation_report_complete \
		type_theory_atlas_daily_automation_report_complete_holds \
		type_theory_atlas_daily_automation_report_complete_gives_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_done \
		type_theory_atlas_daily_automation_report_complete_gives_final_public_theorem \
		type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt \
		type_theory_atlas_daily_automation_report_complete_gives_stage3_utt \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily automation summary entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily automation summary entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily automation summary names are documented and present in Metatheory.v"

check-daily-automation-report-complete:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily automation report-complete entry." && exit 1)
	@if ! rg -q 'daily automation report-complete check: `make check-daily-automation-report-complete`' README.md; then \
		echo "README build status summary does not name the daily automation report-complete check."; \
		exit 1; \
	fi
	@if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q 'type_theory_atlas_daily_automation_report_complete_holds'; then \
		echo "README overview does not name the daily automation report-complete entry."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q 'type_theory_atlas_daily_automation_report_complete_holds'; then \
		echo "README build status summary does not name the daily automation report-complete entry."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_daily_automation_report_complete \
		type_theory_atlas_daily_automation_report_complete_holds \
		type_theory_atlas_daily_automation_report_complete_gives_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_done \
		type_theory_atlas_daily_automation_report_complete_gives_final_public_theorem \
		type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt \
		type_theory_atlas_daily_automation_report_complete_gives_stage3_utt \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily automation report-complete entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing daily automation report-complete entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily automation report-complete names are documented and present in Metatheory.v"

check-daily-automation-report-stage-order:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily automation report stage order." && exit 1)
	@if ! rg -q 'daily automation report stage-order check: `make check-daily-automation-report-stage-order`' README.md; then \
		echo "README build status summary does not name the daily automation report stage-order check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	printf '%s\n' \
		type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt \
		type_theory_atlas_daily_automation_report_complete_gives_stage3_utt \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement > "$$expected"; \
	sed -n '/^- Daily automation report complete:/,/^- Build status checks:/p' README.md | \
		grep -Eo '`type_theory_atlas_daily_automation_report_complete_gives_stage[0-9][A-Za-z0-9_]*`' | \
		tr -d '`' > "$$actual"; \
	missing=0; \
	if ! diff -u "$$expected" "$$actual"; then \
		echo "README daily automation report-complete projections are not in the expected order."; \
		missing=1; \
	fi; \
	for entry in $$(cat "$$expected"); do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing daily automation report stage projection in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
	done; \
	rm -f "$$expected" "$$actual"; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily automation report-complete stage projections are in the expected order."

check-daily-automation-report-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the daily automation report sync." && exit 1)
	@if ! rg -q 'daily automation report sync check: `make check-daily-automation-report-sync`' README.md; then \
		echo "README build status summary does not name the daily automation report sync check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual_readme=$$(mktemp); actual_makefile=$$(mktemp); actual_coq=$$(mktemp); \
	printf '%s\n' \
		type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax \
		type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt \
		type_theory_atlas_daily_automation_report_complete_gives_stage3_utt \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing \
		type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings \
		type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory \
		type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement > "$$expected"; \
	sed -n '/^- Daily automation report complete:/,/^- Build status checks:/p' README.md | \
		grep -Eo '`type_theory_atlas_daily_automation_report_complete_gives_stage[0-9][A-Za-z0-9_]*`' | \
		tr -d '`' > "$$actual_readme"; \
	sed -n '/^check-daily-automation-report-complete:/,/^check-daily-automation-report-stage-order:/p' Makefile | \
		grep -Eo 'type_theory_atlas_daily_automation_report_complete_gives_stage[0-9][A-Za-z0-9_]*' > "$$actual_makefile"; \
	rg -o '^(Theorem|Corollary|Record|Definition|Lemma) type_theory_atlas_daily_automation_report_complete_gives_stage[0-9][A-Za-z0-9_]*' theories/Atlas/Metatheory.v | \
		sed 's/^.* //' > "$$actual_coq"; \
	missing=0; \
	if ! diff -u "$$expected" "$$actual_readme"; then \
		echo "README daily automation report-complete stage projections do not match the expected list."; \
		missing=1; \
	fi; \
	if ! diff -u "$$expected" "$$actual_makefile"; then \
		echo "Makefile daily automation report-complete stage projections do not match the expected list."; \
		missing=1; \
	fi; \
	if ! diff -u "$$expected" "$$actual_coq"; then \
		echo "Coq daily automation report-complete stage projections do not match the expected list."; \
		missing=1; \
	fi; \
	rm -f "$$expected" "$$actual_readme" "$$actual_makefile" "$$actual_coq"; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Daily automation report stage projections match across Coq, README, and Makefile."

check-public-release-manifest:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public release manifest." && exit 1)
	@if ! rg -q 'public release manifest check: `make check-public-release-manifest`' README.md; then \
		echo "README build status summary does not name the public release manifest check."; \
		exit 1; \
	fi
	@if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q 'type_theory_atlas_public_release_manifest_holds'; then \
		echo "README overview does not name the public release manifest entry."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q 'type_theory_atlas_public_release_manifest_holds'; then \
		echo "README build status summary does not name the public release manifest entry."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_public_release_manifest \
		type_theory_atlas_public_release_manifest_holds \
		type_theory_atlas_daily_automation_report_complete_gives_release_manifest \
		type_theory_atlas_public_release_manifest_gives_daily_report \
		type_theory_atlas_public_release_manifest_gives_dashboard \
		type_theory_atlas_public_release_manifest_gives_final_public_theorem \
		type_theory_atlas_public_release_manifest_gives_final_certificate \
		type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax \
		type_theory_atlas_public_release_manifest_gives_stage2_mltt \
		type_theory_atlas_public_release_manifest_gives_stage3_utt \
		type_theory_atlas_public_release_manifest_gives_stage4_tdtt_typing \
		type_theory_atlas_public_release_manifest_gives_stage4_tdtt_dashboard \
		type_theory_atlas_public_release_manifest_gives_stage5_system_embeddings \
		type_theory_atlas_public_release_manifest_gives_stage5_translation_reliability \
		type_theory_atlas_public_release_manifest_gives_stage6_metatheory \
		type_theory_atlas_public_release_manifest_gives_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing public release manifest entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing public release manifest entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Public release manifest names are documented and present in Metatheory.v."

check-public-release-manifest-stage-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking public release manifest stage sync." && exit 1)
	@if ! rg -q 'public release manifest stage-sync check: `make check-public-release-manifest-stage-sync`' README.md; then \
		echo "README build status summary does not name the public release manifest stage-sync check."; \
		exit 1; \
	fi
	@expected_projections=$$(mktemp); expected_fields=$$(mktemp); \
	coq_projection_actual=$$(mktemp); coq_field_actual=$$(mktemp); \
	readme_projection_actual=$$(mktemp); \
	printf '%s\n' \
		type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax \
		type_theory_atlas_public_release_manifest_gives_stage2_mltt \
		type_theory_atlas_public_release_manifest_gives_stage3_utt \
		type_theory_atlas_public_release_manifest_gives_stage4_tdtt_typing \
		type_theory_atlas_public_release_manifest_gives_stage4_tdtt_dashboard \
		type_theory_atlas_public_release_manifest_gives_stage5_system_embeddings \
		type_theory_atlas_public_release_manifest_gives_stage5_translation_reliability \
		type_theory_atlas_public_release_manifest_gives_stage6_metatheory > "$$expected_projections"; \
	printf '%s\n' \
		atlas_public_release_manifest_stage1_unified_syntax \
		atlas_public_release_manifest_stage2_mltt \
		atlas_public_release_manifest_stage3_utt \
		atlas_public_release_manifest_stage4_tdtt_typing \
		atlas_public_release_manifest_stage4_tdtt_dashboard \
		atlas_public_release_manifest_stage5_system_embeddings \
		atlas_public_release_manifest_stage5_translation_reliability \
		atlas_public_release_manifest_stage6_metatheory > "$$expected_fields"; \
	sed -n '/^Record type_theory_atlas_public_release_manifest/,/^Theorem type_theory_atlas_public_release_manifest_holds/p' theories/Atlas/Metatheory.v | \
		grep -Eo 'atlas_public_release_manifest_stage[0-9][A-Za-z0-9_]*' > "$$coq_field_actual"; \
	sed -n '/^Corollary type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax/,/^Corollary type_theory_atlas_public_release_manifest_gives_paper_statement/p' theories/Atlas/Metatheory.v | \
		grep -Eo 'type_theory_atlas_public_release_manifest_gives_stage[0-9][A-Za-z0-9_]*' > "$$coq_projection_actual"; \
	sed -n '/^- Public release manifest:/,/^- Build status checks:/p' README.md | \
		grep -Eo '`type_theory_atlas_public_release_manifest_gives_stage[0-9][A-Za-z0-9_]*`' | \
		tr -d '`' > "$$readme_projection_actual"; \
	if ! diff -u "$$expected_fields" "$$coq_field_actual"; then \
		echo "Coq public release manifest stage fields are not in the expected order."; \
		rm -f "$$expected_projections" "$$expected_fields" "$$coq_projection_actual" "$$coq_field_actual" "$$readme_projection_actual"; \
		exit 1; \
	fi; \
	if ! diff -u "$$expected_projections" "$$coq_projection_actual"; then \
		echo "Coq public release manifest stage projections are not in the expected order."; \
		rm -f "$$expected_projections" "$$expected_fields" "$$coq_projection_actual" "$$coq_field_actual" "$$readme_projection_actual"; \
		exit 1; \
	fi; \
	if ! diff -u "$$expected_projections" "$$readme_projection_actual"; then \
		echo "README public release manifest stage projections are not in the expected order."; \
		rm -f "$$expected_projections" "$$expected_fields" "$$coq_projection_actual" "$$coq_field_actual" "$$readme_projection_actual"; \
		exit 1; \
	fi; \
	rm -f "$$expected_projections" "$$expected_fields" "$$coq_projection_actual" "$$coq_field_actual" "$$readme_projection_actual"; \
	echo "Public release manifest stage fields and projections match the expected order."

check-public-release-complete:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public release complete certificate." && exit 1)
	@if ! rg -q 'public release complete certificate check: `make check-public-release-complete`' README.md; then \
		echo "README build status summary does not name the public release complete certificate check."; \
		exit 1; \
	fi
	@if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q 'type_theory_atlas_public_release_complete_certificate_holds'; then \
		echo "README overview does not name the public release complete certificate."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Build Status Summary/,/^The expected verification story is:/p' README.md | rg -q 'type_theory_atlas_public_release_complete_certificate_holds'; then \
		echo "README build status summary does not name the public release complete certificate."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		type_theory_atlas_public_release_complete \
		type_theory_atlas_public_release_complete_holds \
		type_theory_atlas_public_release_complete_gives_certificate \
		type_theory_atlas_public_release_complete_certificate \
		type_theory_atlas_public_release_complete_certificate_holds \
		type_theory_atlas_public_release_manifest_gives_complete_certificate \
		type_theory_atlas_public_release_complete_gives_manifest \
		type_theory_atlas_public_release_complete_gives_daily_report \
		type_theory_atlas_public_release_complete_gives_dashboard \
		type_theory_atlas_public_release_complete_gives_final_public_theorem \
		type_theory_atlas_public_release_complete_gives_final_certificate \
		type_theory_atlas_public_release_complete_gives_stage1_unified_syntax \
		type_theory_atlas_public_release_complete_gives_stage2_mltt \
		type_theory_atlas_public_release_complete_gives_stage3_utt \
		type_theory_atlas_public_release_complete_gives_stage4_tdtt_typing \
		type_theory_atlas_public_release_complete_gives_stage4_tdtt_dashboard \
		type_theory_atlas_public_release_complete_gives_stage5_system_embeddings \
		type_theory_atlas_public_release_complete_gives_stage5_translation_reliability \
		type_theory_atlas_public_release_complete_gives_stage6_metatheory \
		type_theory_atlas_public_release_complete_gives_paper_statement; do \
		if ! rg -q "^(Theorem|Corollary|Record|Definition|Lemma) $${entry}\\b" theories/Atlas/Metatheory.v; then \
			echo "Missing public release complete entry in theories/Atlas/Metatheory.v: $$entry"; \
			missing=1; \
		fi; \
		if ! rg -q "$${entry}" README.md; then \
			echo "Missing public release complete entry in README.md: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Public release complete certificate names are documented and present in Metatheory.v."

check-public-homepage-summary:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public homepage summary." && exit 1)
	@if ! rg -q 'public homepage summary check: `make check-public-homepage-summary`' README.md; then \
		echo "README build status summary does not name the public homepage summary check."; \
		exit 1; \
	fi
	@if ! rg -q '^- \[Homepage Summary\]\(#homepage-summary\)' README.md; then \
		echo "README contents does not link the homepage summary section."; \
		exit 1; \
	fi
	@if ! rg -q '^## Homepage Summary$$' README.md; then \
		echo "README does not contain the homepage summary section."; \
		exit 1; \
	fi
	@missing=0; \
	for phrase in \
		'Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory' \
		'Main contribution:' \
		'unified syntax framework' \
		'MLTT' \
		'UTT' \
		'TDTT' \
		'system translations' \
		'metatheory' \
		'type_theory_atlas_public_release_complete_holds' \
		'type_theory_atlas_public_release_complete_certificate_holds' \
		'type_theory_atlas_public_release_manifest_holds'; do \
		if ! sed -n '/^## Homepage Summary/,/^## Public Release Citation/p' README.md | rg -q "$$phrase"; then \
			echo "Homepage summary is missing: $$phrase"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Public homepage summary names the contribution, stage route, and Coq release manifest."

check-public-homepage-verification:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public homepage verification note." && exit 1)
	@if ! rg -q 'public homepage verification check: `make check-public-homepage-verification`' README.md; then \
		echo "README build status summary does not name the public homepage verification check."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Public Release Citation/p' README.md | rg -q 'Verification entry point:'; then \
		echo "Homepage summary does not name the verification entry point."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Public Release Citation/p' README.md | rg -q '`make check`'; then \
		echo "Homepage summary does not name make check as the verification entry point."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Public Release Citation/p' README.md | rg -q 'complete verification'; then \
		echo "Homepage summary does not describe make check as complete verification."; \
		exit 1; \
	fi
	@echo "Public homepage summary names make check as the complete verification entry point."

check-public-github-homepage-snippet:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the GitHub homepage snippet." && exit 1)
	@if ! rg -q 'public GitHub homepage snippet check: `make check-public-github-homepage-snippet`' README.md; then \
		echo "README build status summary does not name the public GitHub homepage snippet check."; \
		exit 1; \
	fi
	@if ! rg -q '^- \[GitHub Homepage Snippet\]\(#github-homepage-snippet\)' README.md; then \
		echo "README contents does not link the GitHub homepage snippet section."; \
		exit 1; \
	fi
	@if ! rg -q '^## GitHub Homepage Snippet$$' README.md; then \
		echo "README does not contain the GitHub homepage snippet section."; \
		exit 1; \
	fi
	@missing=0; \
	for phrase in \
		'Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory' \
		'Core contribution:' \
		'unified syntax framework -> MLTT -> UTT -> TDTT -> system translations -> metatheory' \
		'type_theory_atlas_public_release_manifest_holds' \
		'type_theory_atlas_public_release_complete_certificate_holds' \
		'type_theory_atlas_public_release_complete_holds' \
		'make check-public-release-final-package' \
		'make check' \
		'https://github.com/yunbaoatxtu/type-theory-atlas-in-coq'; do \
		if ! sed -n '/^## GitHub Homepage Snippet/,/^## Public Release Citation/p' README.md | rg -q "$$phrase"; then \
			echo "GitHub homepage snippet is missing: $$phrase"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "GitHub homepage snippet names the contribution, release theorem, and verification commands."

check-public-github-repository-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking GitHub repository sync." && exit 1)
	@if ! rg -q 'public GitHub repository sync check: `make check-public-github-repository-sync`' README.md; then \
		echo "README build status summary does not name the public GitHub repository sync check."; \
		exit 1; \
	fi
	@expected='https://github.com/yunbaoatxtu/type-theory-atlas-in-coq'; \
	if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		actual=$$(git remote get-url origin | sed 's#git@github.com:#https://github.com/#; s#\.git$$##'); \
		if [ "$$actual" != "$$expected" ]; then \
			echo "Git origin remote does not match the public repository URL."; \
			echo "expected: $$expected"; \
			echo "actual:   $$actual"; \
			exit 1; \
		fi; \
	fi; \
	for section in \
		'/^## GitHub Homepage Snippet/,/^## Public Release Citation/p' \
		'/^## Public Release Citation/,/^## Build Status Summary/p'; do \
		if ! sed -n "$$section" README.md | rg -q "$$expected"; then \
			echo "README public release section does not name the repository URL: $$expected"; \
			exit 1; \
		fi; \
	done; \
	echo "GitHub repository URL matches README public release references."

check-public-release-citation:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public release citation." && exit 1)
	@if ! rg -q 'public release citation check: `make check-public-release-citation`' README.md; then \
		echo "README build status summary does not name the public release citation check."; \
		exit 1; \
	fi
	@if ! rg -q '^## Public Release Citation$$' README.md; then \
		echo "README does not contain the public release citation section."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | rg -q 'Type Theory Atlas in Coq: From MLTT and UTT to Temporal Dependent Type Theory'; then \
		echo "Public release citation does not name the project title."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | rg -q 'https://github.com/yunbaoatxtu/type-theory-atlas-in-coq'; then \
		echo "Public release citation does not name the GitHub repository."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | rg -q 'type_theory_atlas_public_release_manifest_holds'; then \
		echo "Public release citation does not name the public release manifest theorem."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | rg -q 'type_theory_atlas_public_release_complete_holds'; then \
		echo "Public release citation does not name the public release complete theorem."; \
		exit 1; \
	fi
	@echo "Public release citation snippet names the title, homepage, Coq release manifest, and complete theorem."

check-public-release-citation-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking public release citation sync." && exit 1)
	@if ! rg -q 'public release citation sync check: `make check-public-release-citation-sync`' README.md; then \
		echo "README build status summary does not name the public release citation sync check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	{ \
		sed -n 's/^Theorem \(type_theory_atlas_public_release_manifest_holds\) :/\1/p' theories/Atlas/Metatheory.v; \
		sed -n 's/^Theorem \(type_theory_atlas_public_release_complete_certificate_holds\) :/\1/p' theories/Atlas/Metatheory.v; \
		sed -n 's/^Theorem \(type_theory_atlas_public_release_complete_holds\) :/\1/p' theories/Atlas/Metatheory.v; \
	} | sort -u > "$$expected"; \
	{ \
		sed -n '/^## Homepage Summary/,/^## Public Release Citation/p' README.md | \
			grep -Eo 'Final Coq entry point: `[^`]+`' | \
			grep -Eo '`[A-Za-z_][A-Za-z0-9_]*`' | tr -d '`'; \
		sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | \
			grep -Eo 'Coq release manifest: [A-Za-z_][A-Za-z0-9_]*' | \
			sed 's/Coq release manifest: //'; \
		sed -n '/^## Public Release Citation/,/^## Build Status Summary/p' README.md | \
			grep -Eo 'Coq release complete: [A-Za-z_][A-Za-z0-9_]*' | \
			sed 's/Coq release complete: //'; \
		sed -n '/^The current public release manifest entry point is/,/^The current daily automation report-complete entry point is/p' README.md | \
			grep -Eo '`[A-Za-z_][A-Za-z0-9_]*`' | tr -d '`'; \
	} | sort -u > "$$actual"; \
	if [ "$$(wc -l < "$$expected" | tr -d ' ')" -ne 3 ]; then \
		echo "Coq public release manifest/complete declarations are missing or ambiguous."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi; \
	if diff -u "$$expected" "$$actual"; then \
		echo "Public release citation references match the Coq release manifest, complete certificate, and complete theorem."; \
		rm -f "$$expected" "$$actual"; \
	else \
		echo "Public release citation references do not match the Coq release manifest, complete certificate, and complete theorem."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-public-readme-release-package:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public README release package." && exit 1)
	@if ! rg -q 'public README release package check: `make check-public-readme-release-package`' README.md; then \
		echo "README build status summary does not name the public README release package check."; \
		exit 1; \
	fi
	@$(MAKE) check-public-release-manifest
	@$(MAKE) check-public-release-manifest-stage-sync
	@$(MAKE) check-public-release-complete
	@$(MAKE) check-public-homepage-summary
	@$(MAKE) check-public-homepage-verification
	@$(MAKE) check-public-github-homepage-snippet
	@$(MAKE) check-public-github-repository-sync
	@$(MAKE) check-public-release-citation
	@$(MAKE) check-public-release-citation-sync
	@if ! sed -n '/^## Homepage Summary/,/^## Build Status Summary/p' README.md | rg -q 'type_theory_atlas_public_release_manifest_holds'; then \
		echo "Public README release package does not include the release manifest theorem."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Build Status Summary/p' README.md | rg -q 'type_theory_atlas_public_release_complete_certificate_holds'; then \
		echo "Public README release package does not include the release complete certificate."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Build Status Summary/p' README.md | rg -q 'type_theory_atlas_public_release_complete_holds'; then \
		echo "Public README release package does not include the release complete theorem."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Build Status Summary/p' README.md | rg -q '`make check`'; then \
		echo "Public README release package does not include the complete verification entry point."; \
		exit 1; \
	fi
	@if ! sed -n '/^## Homepage Summary/,/^## Build Status Summary/p' README.md | rg -q 'https://github.com/yunbaoatxtu/type-theory-atlas-in-coq'; then \
		echo "Public README release package does not include the GitHub repository."; \
		exit 1; \
	fi
	@if ! sed -n '/^The expanded form is:/,/^## Build/p' README.md | rg -q '^make check-public-(readme-release|release-final)-package$$'; then \
		echo "README expanded verification form does not include the public README release package check or final release wrapper."; \
		exit 1; \
	fi
	@echo "Public README release package checks homepage summary, GitHub snippet, citation, citation sync, manifest, release-complete certificate, stage field/projection order, and verification entry."

check-public-release-final-entry:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the final public release entry." && exit 1)
	@if ! rg -q 'public release final entry check: `make check-public-release-final-entry`' README.md; then \
		echo "README build status summary does not name the public release final entry check."; \
		exit 1; \
	fi
	@if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q '^- final public release verification:'; then \
		echo "README top-level entry points do not name the final public release verification target."; \
		exit 1; \
	fi
	@if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q '`make check-public-release-final-package`'; then \
		echo "README top-level entry points do not point to make check-public-release-final-package."; \
		exit 1; \
	fi
	@if ! sed -n '/^The expected verification story is:/,/^## Build/p' README.md | rg -q 'public release final package check: `make check-public-release-final-package`'; then \
		echo "README verification story does not name the final public release package check."; \
		exit 1; \
	fi
	@if ! sed -n '/^check:/,/^check-readme-entries:/p' Makefile | grep -Fq '$$(MAKE) check-public-release-final-package'; then \
		echo "Makefile check target does not run check-public-release-final-package."; \
		exit 1; \
	fi
	@echo "Final public release entry is exposed in README and covered by make check."

check-public-release-navigation:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking public release README navigation." && exit 1)
	@if ! rg -q 'public release navigation check: `make check-public-release-navigation`' README.md; then \
		echo "README build status summary does not name the public release navigation check."; \
		exit 1; \
	fi
	@missing=0; \
	for link in \
		'^- \[Homepage Summary\]\(#homepage-summary\)' \
		'^- \[GitHub Homepage Snippet\]\(#github-homepage-snippet\)' \
		'^- \[Public Release Citation\]\(#public-release-citation\)' \
		'^- \[Build Status Summary\]\(#build-status-summary\)' \
		'^- \[Build\]\(#build\)'; do \
		if ! sed -n '/^## Contents/,/^## Entry Consistency Checklist/p' README.md | rg -q "$$link"; then \
			echo "README contents is missing public release navigation link: $$link"; \
			missing=1; \
		fi; \
	done; \
	for section in \
		'^## Homepage Summary$$' \
		'^## GitHub Homepage Snippet$$' \
		'^## Public Release Citation$$' \
		'^## Build Status Summary$$' \
		'^## Build$$'; do \
		if ! rg -q "$$section" README.md; then \
			echo "README is missing public release section: $$section"; \
			missing=1; \
		fi; \
	done; \
	if ! sed -n '/^Current top-level entry points:/,/^## Contents/p' README.md | rg -q '^- current build status: see `Build Status Summary`\.'; then \
		echo "README top-level entry points do not point readers to Build Status Summary."; \
		missing=1; \
	fi; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi; \
	echo "Public release README navigation links homepage snippet, citation, build status, and build sections."

check-public-readme-release-map:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public README release map." && exit 1)
	@if ! rg -q 'public README release map check: `make check-public-readme-release-map`' README.md; then \
		echo "README build status summary does not name the public README release map check."; \
		exit 1; \
	fi
	@expected_links=$$(mktemp); actual_links=$$(mktemp); \
	expected_sections=$$(mktemp); actual_sections=$$(mktemp); \
	printf '%s\n' \
		'- [Homepage Summary](#homepage-summary)' \
		'- [GitHub Homepage Snippet](#github-homepage-snippet)' \
		'- [Public Release Citation](#public-release-citation)' \
		'- [Build Status Summary](#build-status-summary)' \
		'- [Build](#build)' > "$$expected_links"; \
	sed -n '/^## Contents/,/^## Entry Consistency Checklist/p' README.md | \
		grep -E '^- \[(Homepage Summary|GitHub Homepage Snippet|Public Release Citation|Build Status Summary|Build)\]' > "$$actual_links"; \
	printf '%s\n' \
		'## Homepage Summary' \
		'## GitHub Homepage Snippet' \
		'## Public Release Citation' \
		'## Build Status Summary' \
		'## Build' > "$$expected_sections"; \
	sed -n '/^## Homepage Summary/,/^The last command should/p' README.md | \
		grep -E '^## (Homepage Summary|GitHub Homepage Snippet|Public Release Citation|Build Status Summary|Build)$$' > "$$actual_sections"; \
	if ! diff -u "$$expected_links" "$$actual_links"; then \
		echo "README public release contents links are not in the expected order."; \
		rm -f "$$expected_links" "$$actual_links" "$$expected_sections" "$$actual_sections"; \
		exit 1; \
	fi; \
	if ! diff -u "$$expected_sections" "$$actual_sections"; then \
		echo "README public release sections are not in the expected order."; \
		rm -f "$$expected_links" "$$actual_links" "$$expected_sections" "$$actual_sections"; \
		exit 1; \
	fi; \
	rm -f "$$expected_links" "$$actual_links" "$$expected_sections" "$$actual_sections"; \
	echo "Public README release map matches contents links and section order."

check-public-release-checklist:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the public release checklist." && exit 1)
	@if ! rg -q 'public release checklist check: `make check-public-release-checklist`' README.md; then \
		echo "README build status summary does not name the public release checklist check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	printf '%s\n' \
		'- release content package: `make check-public-release-final-package`;' \
		'- full daily verification: `make check`;' \
		'- clean Coq rebuild: `make clean && make -j1`;' \
		'- unfinished-proof scan: `make check-no-admits`;' \
		'- Coq release manifest theorem: `type_theory_atlas_public_release_manifest_holds`;' \
		'- Coq release complete theorem: `type_theory_atlas_public_release_complete_holds`;' \
		'- Coq release complete certificate: `type_theory_atlas_public_release_complete_certificate_holds`.' > "$$expected"; \
	sed -n '/^The public release checklist is:/,/^The expected verification story is:/p' README.md | \
		grep -E '^- (release content package|full daily verification|clean Coq rebuild|unfinished-proof scan|Coq release manifest theorem|Coq release complete theorem|Coq release complete certificate):' > "$$actual"; \
	if diff -u "$$expected" "$$actual"; then \
		echo "Public release checklist matches the reusable release commands and theorem."; \
		rm -f "$$expected" "$$actual"; \
	else \
		echo "Public release checklist does not match the expected release commands and theorem."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-public-source-hygiene:
	@command -v git >/dev/null || \
		(echo "Missing git: install git before checking public source hygiene." && exit 1)
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking public source hygiene." && exit 1)
	@if ! rg -q 'public source hygiene check: `make check-public-source-hygiene`' README.md; then \
		echo "README build status summary does not name the public source hygiene check."; \
		exit 1; \
	fi
	@missing=0; \
	for entry in \
		'.DS_Store' \
		'.Makefile.coq.d' \
		'*.aux' \
		'*.glob' \
		'*.vo' \
		'*.vok' \
		'*.vos' \
		'.lia.cache' \
		'Makefile.coq' \
		'Makefile.coq.conf'; do \
		if ! grep -Fxq "$$entry" .gitignore; then \
			echo "Missing generated-file ignore rule in .gitignore: $$entry"; \
			missing=1; \
		fi; \
	done; \
	if [ "$$missing" -ne 0 ]; then exit 1; fi
	@if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then \
		tracked=$$(git ls-files | grep -E '(^|/)\.DS_Store$$|(^|/)\.Makefile\.coq\.d$$|(^|/)\.lia\.cache$$|(^|/)Makefile\.coq(\.conf)?$$|\.aux$$|\.glob$$|\.vo$$|\.vok$$|\.vos$$' || true); \
		if [ -n "$$tracked" ]; then \
			echo "Tracked generated files should be removed from the public source package:"; \
			echo "$$tracked"; \
			exit 1; \
		fi; \
		echo "Public source package has no tracked generated Coq or platform artifacts."; \
	else \
		echo "Not inside a Git worktree; generated-file ignore rules are present."; \
	fi

check-public-release-final-package:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the final public release package." && exit 1)
	@if ! rg -q 'public release final package check: `make check-public-release-final-package`' README.md; then \
		echo "README build status summary does not name the public release final package check."; \
		exit 1; \
	fi
	@$(MAKE) check-public-release-final-entry
	@$(MAKE) check-public-readme-release-map
	@$(MAKE) check-public-release-navigation
	@$(MAKE) check-public-release-checklist
	@$(MAKE) check-public-source-hygiene
	@$(MAKE) check-public-readme-release-package
	@$(MAKE) check-expanded-verification-sync
	@$(MAKE) check-help-readme-sync
	@$(MAKE) check-phony-help-sync
	@echo "Final public release package checks release content, release-complete certificate, source hygiene, release checklist, README release map, README navigation, expanded verification, help/README sync, and .PHONY/help sync."

check-expanded-verification-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking the expanded verification sync." && exit 1)
	@if ! rg -q 'expanded verification sync check: `make check-expanded-verification-sync`' README.md; then \
		echo "README build status summary does not name the expanded verification sync check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	sed -n '/^check:/,/^check-readme-entries:/p' Makefile | \
		sed -n 's/^\t$$(MAKE) //p' | \
		awk ' \
			$$0 == "clean" { clean = 1; next } \
			$$0 == "-j1 all" { \
				if (clean) { print "make clean && make -j1"; clean = 0 } \
				else { print "make -j1" } \
				next \
			} \
			{ \
				if (clean) { print "make clean"; clean = 0 } \
				print "make " $$0 \
			} \
			END { if (clean) print "make clean" } \
		' > "$$expected"; \
	sed -n '/^The expanded form is:/,/^The last command should/p' README.md | \
		grep -E '^make( |$$)' > "$$actual"; \
	if diff -u "$$expected" "$$actual"; then \
		echo "README expanded verification form matches the Makefile check target order."; \
		rm -f "$$expected" "$$actual"; \
	else \
		echo "README expanded verification form does not match the Makefile check target order."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-help-readme-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking help/README target sync." && exit 1)
	@if ! rg -q 'help/README target sync check: `make check-help-readme-sync`' README.md; then \
		echo "README build status summary does not name the help/README target sync check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	$(MAKE) -s help | \
		grep -Eo '^  make (help|check[^ ]*)' | \
		sed 's/^  //' > "$$expected"; \
	sed -n '/^The expected verification story is:/,/^## Build/p' README.md | \
		grep -Eo '`make (help|check[^` ]*)`' | \
		tr -d '`' > "$$actual"; \
	if diff -u "$$expected" "$$actual"; then \
		echo "make help targets match the README verification target list."; \
		rm -f "$$expected" "$$actual"; \
	else \
		echo "make help targets do not match the README verification target list."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-phony-help-sync:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before checking .PHONY/help target sync." && exit 1)
	@if ! rg -q 'phony/help target sync check: `make check-phony-help-sync`' README.md; then \
		echo "README build status summary does not name the .PHONY/help target sync check."; \
		exit 1; \
	fi
	@expected=$$(mktemp); actual=$$(mktemp); \
	sed -n 's/^\.PHONY: //p' Makefile | \
		tr ' ' '\n' | \
		awk '$$0 == "all" { print "make"; next } { print "make " $$0 }' | \
		sort > "$$expected"; \
	$(MAKE) -s help | \
		grep -Eo '^  make( [^[:space:]]+)?' | \
		sed 's/^  //; s/[[:space:]]*$$//' | \
		sort > "$$actual"; \
	if diff -u "$$expected" "$$actual"; then \
		echo ".PHONY targets match the make help target list."; \
		rm -f "$$expected" "$$actual"; \
	else \
		echo ".PHONY targets do not match the make help target list."; \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-project-order:
	@expected=$$(mktemp); \
	actual=$$(mktemp); \
	printf '%s\n' \
		'theories/Atlas/Syntax.v' \
		'theories/Atlas/Ops.v' \
		'theories/Atlas/Context.v' \
		'theories/Atlas/DefEq.v' \
		'theories/Atlas/MLTT.v' \
		'theories/Atlas/Weakening.v' \
		'theories/Atlas/Substitution.v' \
		'theories/Atlas/UTT.v' \
		'theories/Atlas/UTTWeakening.v' \
		'theories/Atlas/UTTSubstitution.v' \
		'theories/Atlas/TemporalContext.v' \
		'theories/Atlas/TDTT.v' \
		'theories/Atlas/TDTTTemporalWeakening.v' \
		'theories/Atlas/TDTTTemporalSubstitution.v' \
		'theories/Atlas/TDTTWeakening.v' \
		'theories/Atlas/TDTTSubstitution.v' \
		'theories/Atlas/DelayedSubstitution.v' \
		'theories/Atlas/Translations.v' \
		'theories/Atlas/Inversion.v' \
		'theories/Atlas/Metatheory.v' > "$$expected"; \
	grep '^theories/Atlas/.*\.v$$' _CoqProject > "$$actual"; \
	if diff -u "$$expected" "$$actual"; then \
		echo "_CoqProject file order matches README Layer Summary."; \
		rm -f "$$expected" "$$actual"; \
	else \
		rm -f "$$expected" "$$actual"; \
		exit 1; \
	fi

check-no-admits:
	@command -v rg >/dev/null || \
		(echo "Missing rg: install ripgrep before scanning proof markers." && exit 1)
	@if rg -n "\b(Admitted|admit|Abort)\b" theories/Atlas -g "*.v"; then \
		echo "Found unfinished proof markers."; \
		exit 1; \
	else \
		echo "No unfinished proof markers found."; \
	fi

clean:
	@if [ -f Makefile.coq ]; then $(PLATFORM_ENV) $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf
