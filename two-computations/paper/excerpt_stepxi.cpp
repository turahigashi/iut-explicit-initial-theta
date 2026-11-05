StepXiCertificate step_xi(const Representation& rep, const QPilot& qp)
{
    StepXiCertificate X;
    X.margin = rep.minus_log_theta - qp.minus_log_q;
    X.contained = X.margin >= 0;
    X.how = "reverse-computed from the conclusion: the two log-volumes of this datum were compared. A Step (xi) "
            "derived from Theorem 3.11 would give the containment for every initial Theta-datum without comparing "
            "numbers";
    OracleLedger::record("step-xi", "Step (xi): the q-pilot of ddagger lies in the hull of the possible images", X.how);
    return X;
}
