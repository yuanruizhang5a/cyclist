I assume you mean certificate_sound in Rocq-copy/Cyclic/Framework.v:718.
The central mathematical idea is:
If a judgment were false, the certificate would let us move to another false judgment with a strictly smaller well-founded measure. Such descent cannot continue forever, so no judgment—and in particular the root—can be false.
Here is how the code turns that idea into a proof.
1. What the theorem says
Write \(J_i\) for the judgment at graph node \(i\), and \(J_{\mathrm{root}}\) for the declared root judgment.
A world \(w\) is a semantic state in which judgments are evaluated. Thus
\[
\operatorname{holds}(J_i,w)
\]
means “\(J_i\) is true in world \(w\).”
The theorem states
\[
\operatorname{check\_certificate}(c)=\mathrm{true}
\quad\Longrightarrow\quad
\forall w,\ \operatorname{holds}(J_{\mathrm{root}},w).
\]
The difficulty is that the proof graph can contain cycles. We cannot simply prove validity by induction on the graph’s shape. Instead, we induct on a semantic descent measure.
2. A false judgment must have a false successor
The certificate contains an obligation called cert_advance (Framework.v:598).
Mathematically, it says that whenever \(i\) is a valid node index and \(J_i\) is false in \(w\), there exist a successor \(j\), a world \(w'\), and an edge \(e:i\to j\) such that
\[
\neg\operatorname{holds}(J_j,w').
\]
Moreover, the edge respects the semantic ranks attached to trace tags.
For a tag \(a\) at node \(i\), write
\[
r_i(w,a)=T.\operatorname{rank}(J_i,w,a)\in\mathbb N.
\]
Then:
- If \((a,b)\) is a valid tag pair on the edge,
\[
r_j(w',b)\le r_i(w,a).
\]
- If \((a,b)\) is a progressing tag pair,
\[
r_j(w',b)<r_i(w,a).
\]
So falsity can be followed through the graph, while ranks obey the edge annotations.
But non-increasing ranks alone are insufficient: a rank could remain constant forever. The trace witness supplies the additional decrease needed.
3. The witness supplies a lexicographic measure
At each node \(i\), the witness supplies:
- an optional selected tag \(t_i\);
- an auxiliary potential \(p_i\in\mathbb N\).
The proof defines the measure (combined_measure, line 666) as
\[
M(i,w)=
\begin{cases}
(1,p_i,0), & \text{if no tag is selected},\\2mm
(0,r_i(w,t_i),p_i), & \text{if a tag is selected}.
\end{cases}
\]
These triples are ordered lexicographically, with the first coordinate most significant:
\[
(x_1,x2,x3)<{\mathrm{lex}}(y1,y2,y3)
\]
when the first differing coordinate is smaller.
The first coordinate distinguishes two phases:
- \(1\): before selecting a trace;
- \(0\): following a selected trace.
Selecting a trace therefore decreases the measure immediately, regardless of its initial rank.
The order is well founded because it is a finite lexicographic product of the well-founded order \(<\) on \(\mathbb N\). This is measure_lt_wf at line 653.
4. Why every false-successor step strictly decreases the measure
This is the key lemma, certificate_step_decreases (Framework.v:677):
\[
\neg\operatorname{holds}(J_i,w)
\quad\Longrightarrow\quad
\exists j,w',\
\neg\operatorname{holds}(J_j,w')
\ \land\
M(j,w')<_{\mathrm{lex}}M(i,w).
\]
To prove it, the code first obtains a false successor using cert_advance.
Because that successor is false, cert_false_live says it is live: it lies in a region where arbitrarily continuing the graph is possible. Consequently, cert_trace_transition applies to the chosen edge.
There are four cases.
Case A: No tag → no tag
The trace-transition condition requires
\[
p_j<p_i.
\]
Hence
\[
(1,p_j,0)<_{\mathrm{lex}}(1,p_i,0).
\]
Case B: No tag → selected tag
The phase changes from \(1\) to \(0\):
\[
(0,r_j(w',t_j),p_j)
<_{\mathrm{lex}}
(1,p_i,0).
\]
No comparison of semantic ranks is needed.
Case C: Selected tag → no tag
The trace-transition condition forbids this case.
Once a trace is selected, it cannot be abandoned.
Case D: Selected tag → selected tag
Let the selected tags be \(a\) and \(b\). The witness requires a valid pair \((a,b)\), together with either:
1. Semantic progress:
\[
r_j(w',b)<r_i(w,a),
\]
which directly decreases the second coordinate; or
2. Potential progress:
\[
p_j<p_i,
\]
while validity ensures
\[
r_j(w',b)\le r_i(w,a).
\]
If the rank decreases, the second coordinate decreases. If the rank stays equal, the third coordinate decreases.
Thus, in every permitted case,
\[
M(j,w')<_{\mathrm{lex}}M(i,w).
\]
5. The final proof: well-founded induction excludes falsity
The actual theorem uses well-founded induction rather than explicitly constructing an infinite path.
Define
\[
P(m):
\quad
\text{there is no false node-world pair }(i,w)
\text{ with }M(i,w)=m.
\]
Assume inductively that \(P(m')\) holds for every \(m'<m\).
Suppose, toward a contradiction, that
\[
M(i,w)=m
\quad\text{and}\quad
\neg\operatorname{holds}(J_i,w).
\]
The step-decrease lemma produces \(j,w'\) with
\[
\neg\operatorname{holds}(J_j,w')
\quad\text{and}\quad
M(j,w')<m.
\]
But the induction hypothesis says that no false pair can have that smaller measure. Contradiction.
Therefore \(P(m)\) holds for every measure \(m\).
Finally, the certificate guarantees that node \(0\) exists and
\[
J0=J{\mathrm{root}}.
\]
So the root cannot be false in any world. Using classical double-negation elimination (NNPP), the proof concludes
\[
\boxed{\forall w,\ \operatorname{holds}(J_{\mathrm{root}},w).}
\]
An important detail about this implementation
The theorem begins with:
intros _ w.
The _ means that the Boolean acceptance assumption is not used in this proof.
The reason is that certificate is already a proof-carrying record: it contains kernel-checked proofs of cert_advance, cert_false_live, cert_trace_transition, and the root obligations. Those fields already suffice for the mathematical soundness argument.
Thus the precise dependency here is:
\[
\boxed{
\text{certificate’s semantic obligations}
\ \Longrightarrow\
\text{strict well-founded descent from any false node}
\ \Longrightarrow\
\text{root validity}.
}
\]
The Boolean check is present in the theorem’s interface, but the proof of certificate_sound itself derives validity from the evidence stored in the certificate.