import logging
from typing import List

from constants import SecurityProperty, PROPERTY_TO_STR
from input import Input
from output import AnalysisResult
from solving_newcases import WeakImmunityStrategySolver, WeakerImmunityStrategySolver, CollusionResilienceStrategySolver, \
    PracticalityStrategySolver2


def analyze_input(checked_input: Input,
                  analyzed_properties: List[SecurityProperty],
                  generate_preconditions: bool,
                  generate_counterexamples: bool) -> List[AnalysisResult]:
    logging.info(
        f"input OK, checking {len(checked_input.honest_histories)} histories..."
    )

    results = []
    for honest_history in checked_input.honest_histories:
        wi_res, weri_res, cr_res, p_res = None, None, None, None
        logging.info(f"history {honest_history}")

        if SecurityProperty.WEAK_IMMUNITY in analyzed_properties:
            logging.info("checking weak immunity")
            wi_solver = WeakImmunityStrategySolver(
                checked_input,
                honest_history,
                generate_preconditions,
                generate_counterexamples
            )
            wi_res = wi_solver.solve()

        if SecurityProperty.WEAKER_IMMUNITY in analyzed_properties:
            logging.info("checking weaker immunity")
            weri_solver = WeakerImmunityStrategySolver(
                checked_input,
                honest_history,
                generate_preconditions,
                generate_counterexamples
            )
            weri_res = weri_solver.solve()

        if SecurityProperty.COLLUSION_RESILIENCE in analyzed_properties:
            logging.info("checking collusion resilience")
            cr_solver = CollusionResilienceStrategySolver(
                checked_input,
                honest_history,
                generate_preconditions,
                generate_counterexamples
            )
            cr_res = cr_solver.solve()

        if SecurityProperty.PRACTICALITY in analyzed_properties:
            logging.info("checking practicality")
            pr_solver = PracticalityStrategySolver2(
                checked_input,
                honest_history,
                generate_preconditions,
                generate_counterexamples
            )
            p_res = pr_solver.solve()

        results.append(AnalysisResult(honest_history, wi_res, weri_res, cr_res, p_res))

    # nice summary of the check
    logging.info("####### Summary: ######")
    for result in results:
        logging.info(f"Honest history {result.honest_history}")

        for security_property in analyzed_properties:
            property_result = result.get_property_result(security_property)
            found_strategies = property_result.strategies
            found_counterexample_cases = property_result.counterexamples
            gen_preconditions = property_result.generated_preconditions

            if found_counterexample_cases:
                logging.info(f"-- doesn't have {PROPERTY_TO_STR[security_property]}")

            elif len(found_strategies) == 1:
                logging.info(
                    f"-- has {PROPERTY_TO_STR[security_property]} (one strategy)" if not gen_preconditions
                    else f"-- has {PROPERTY_TO_STR[security_property]} if {gen_preconditions} (one strategy)"
                )

            else:

                assert len(found_strategies) > 0, "no strategy but also no unsat case found"
                logging.info(
                    f"-- has {PROPERTY_TO_STR[security_property]} "
                    f"with different strategies for cases" if not gen_preconditions
                    else f"-- has {PROPERTY_TO_STR[security_property]} if {gen_preconditions} "
                         f"with different strategies for cases"
                )

                for i, cws in enumerate(found_strategies):
                    logging.info(f"---- case {i}: {[str(c) for c in cws.ordering_case]}")

    return results
