// (C) cyclotomic rigidity at level N. In the theta group the commutator pairing a |-> [t, a] identifies the
// cyclotome mu_N of the Z-covering with the central cyclotome Delta_Theta ([EtTh] Prop. 2.12; lana-agents/iut,
// Iut/EtaleTheta/Heisenberg.lean, cyclotomicRigidity_aut). The c-coordinate of [t, a_1] is the coordinate of the
// image of the generator a_1: the unit by which the theater's coordinates on Delta_Theta differ from those of mu_N.
u64 rigidity_unit(const ThetaGroupBox& G)
{
    const ThetaGroupElement t = G.generator_t(), a = G.generator_a();
    const ThetaGroupElement c = G.mul(G.mul(t, a), G.mul(G.inv(t), G.inv(a)));
    if (c.a != 0 || c.b != 0 || c.c == 0) throw std::runtime_error("the commutator is not a nonzero central element");
    return c.c;
}

    ...

    // (C)-(D) The theta values qq^(j^2) at the bad places, from their Kummer classes in Delta_Theta.
    for (int i = 0; i < n; i++) {
        const EtalePlace& P = in.places[i];
        if (!P.bad) continue;
        if (!R.local[i].known || !P.theta_group || (int)P.theta.size() != ls)
            throw std::runtime_error("incomplete etale-like data at " + P.name);
        const u64 g = use_rigidity_ ? rigidity_unit(*P.theta_group) : 1;
        const u64 ginv = invmod(g);
        R.rigidity[i] = g;
        std::vector<u64> val(ls);                    // ord_{K_v}(qq^(j^2)) mod N
        for (int j = 1; j <= ls; j++) val[j - 1] = mulmod(P.theta[j - 1].value, ginv);
        for (int j = 1; j <= ls; j++)
            if (val[j - 1] != mulmod(val[0], (u64)j * j)) R.gaussian_ok = false;
        R.theta_ord[i] = (double)val[0] / R.local[i].e;   // ord_p(qq) = ord_{K_v}(qq) / e; the valuations are << N
    }
