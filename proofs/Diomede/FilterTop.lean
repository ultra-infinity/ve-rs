/- Specs of `diomede::filter`: the verdict on an IP packet. -/
import Diomede.DnsTop
import Diomede.TlsTop
import Diomede.BlocklistTop
import Net.ManualTop

open Aeneas Aeneas.Std Result untrusted

namespace diomede

/-! ## Determinism of the decoders -/

/-- A query's name is determined by the message. -/
theorem dns.DnsQuery.Spec.text_eq {m : List U8} {q q' : dns.DnsQuery} (h : dns.DnsQuery.Spec m q)
    (h' : dns.DnsQuery.Spec m q') : q.name.text = q'.name.text := by
  obtain ⟨-, -, -, -, -, -, ls, k, hf, -, -, -, ht, -⟩ := h
  obtain ⟨-, -, -, -, -, -, ls', k', hf', -, -, -, ht', -⟩ := h'
  obtain ⟨rfl, -⟩ := hf.unique hf'
  rw [ht, ht']

/-- A ClientHello's server name is determined by the stream. -/
theorem tls.ClientHello.Spec.text_eq {s : List U8} {c c' : tls.ClientHello}
    (h : tls.ClientHello.Spec s c) (h' : tls.ClientHello.Spec s c') :
    c.server_name.map name.Name.text = c'.server_name.map name.Name.text := by
  unfold tls.ClientHello.Spec at h h'
  rcases hs : tls.serverNameN s with _ | _ | hn <;> rw [hs] at h h' <;>
    rcases hc : c.server_name with _ | n <;> rw [hc] at h <;>
    rcases hc' : c'.server_name with _ | n' <;> rw [hc'] at h' <;> simp_all

namespace filter

open blocklist

/-! ## What is blocked -/

/-- The text `n` of a name is blocked by `list`: it is a listed domain or a
    subdomain of one (see `blocklist.blocked_iff`). -/
abbrev BlockedBy (list : Blocklist) (n : List Nat) : Prop :=
  Blocked (vals list.data.val) (endsN list.ends) n

/-- `msg` is a DNS query for a name `list` blocks. -/
def QueryBlocked (list : Blocklist) (msg : List U8) : Prop :=
  ∃ q, dns.DnsQuery.Spec msg q ∧ BlockedBy list q.name.text

/-- `s` starts with a ClientHello for a server name `list` blocks. -/
def HelloBlocked (list : Blocklist) (s : List U8) : Prop :=
  ∃ c n, tls.ClientHello.Spec s c ∧ c.server_name = some n ∧ BlockedBy list n.text

/-! ## DNS -/

/-- **Spec theorem for `<Query as Validate<&[u8]>>::validate`**. -/
@[step]
theorem _root_.diomede.dns.Query.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (msg : Slice U8) :
    dns.Query.Insts.UntrustedValidateSharedASliceU8ValidationError.validate msg
      ⦃ (r : core.result.Result dns.Query ValidationError) =>
        match r with
        | .Ok q => q.msg = msg ∧ dns.DnsQuery.Spec msg.val q.query
        | .Err _ => ∀ q, ¬ dns.DnsQuery.Spec msg.val q ⦄ := by
  unfold dns.Query.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  step as ⟨r, hr⟩
  cases r
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    exact ⟨by simp, hr⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact hr

/-- **Spec theorem for `dns_answer`**: whether `msg` is a query for a
    blocked name and, if so, its NXDOMAIN answer in `answer`, if it fits. -/
@[step]
theorem dns_answer.spec (msg : Untrusted (Slice U8)) (list : Blocklist)
    (answer : Array U8 512#usize) (hb : list.Inv) :
    dns_answer msg list answer ⦃ (r : Option (Option Usize) × Array U8 512#usize) =>
      match r.1 with
      | none => ¬ QueryBlocked list (msg : Slice U8).val
      | some o => ∃ q, dns.DnsQuery.Spec (msg : Slice U8).val q ∧ BlockedBy list q.name.text ∧
          match o with
          | none => True
          | some n => n.val = 12 + q.question_len.val ∧ n.val ≤ 512 ∧
              (r.2.val.take n.val).map (·.val) = dns.answerN (msg : Slice U8).val q ⦄ := by
  unfold dns_answer
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp only [WP.spec_ok]
    rintro ⟨q, hq, -⟩
    exact hr q hq
  | Ok q =>
    obtain ⟨hm, hq⟩ := hr
    have hinv : q.query.name.Inv := hq.2.2.2.2.2.2.choose_spec.choose_spec.2.2.2.1
    simp only
    step with name.Name.as_bytes.spec q.query.name hinv as ⟨s, hs⟩
    step with Blocklist.blocked.spec list hb s as ⟨b, hbl⟩
    split
    · rename_i hbt
      step*
      have hv : vals s.val = q.query.name.text := hs
      refine ⟨q.query, hq, by rw [← hv]; exact hbl.1 hbt, ?_⟩
      rcases o with _ | n
      · trivial
      · obtain ⟨h1, hle, h2, h3, -⟩ := o_post
        refine ⟨h1, by simp_all [Slice.length], ?_⟩
        rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by simp_all [Slice.length]), ← hm, h3]
    · simp only [WP.spec_ok]
      rintro ⟨q', hq', hbq'⟩
      rename_i hbf
      have hv : vals s.val = q'.name.text := hs.trans (hq'.text_eq hq).symm
      exact hbf (hbl.2 (by rw [hv]; exact hbq'))

/-! ## Verdicts -/

@[simp, scalar_tac_simps] theorem dns_PORT_val : dns.PORT.val = 53 := by simp [dns.PORT]
@[simp, scalar_tac_simps] theorem tls_PORT_val : tls.PORT.val = 443 := by simp [tls.PORT]

/-- The reply `out[..n]` to the query `q` in the datagram `u`, over IPv4: from
    the server the query was sent to, back to the client, carrying the
    NXDOMAIN answer. -/
def Reply4 (u : net.udp.Ipv4Udp) (out : List U8) (n : Nat) (q : dns.DnsQuery) : Prop :=
  ∃ r : net.udp.Ipv4Udp, net.udp.Ipv4Udp.Spec (out.take n) r ∧
    r.ip.header.src = u.ip.header.dst ∧ r.ip.header.dst = u.ip.header.src ∧
    (r.header.src_port : U16).val = 53 ∧ r.header.dst_port = u.header.src_port ∧
    (r.payload : Slice U8).val.map (·.val) = dns.answerN (u.payload : Slice U8).val q

/-- The reply `out[..n]` to the query `q` in the datagram `u`, over IPv6. -/
def Reply6 (u : net.udp.Ipv6Udp) (out : List U8) (n : Nat) (q : dns.DnsQuery) : Prop :=
  ∃ r : net.udp.Ipv6Udp, net.udp.Ipv6Udp.Spec (out.take n) r ∧
    r.ip.header.src = u.ip.header.dst ∧ r.ip.header.dst = u.ip.header.src ∧
    (r.header.src_port : U16).val = 53 ∧ r.header.dst_port = u.header.src_port ∧
    (r.payload : Slice U8).val.map (·.val) = dns.answerN (u.payload : Slice U8).val q

/-- The verdict on the DNS message `msg` sent to UDP port `port`: a query
    for a blocked name to port 53 is answered (`reply n q` describes the
    answer `out[..n]`), or dropped if the answer does not fit; anything else
    passes. -/
def DnsVerdict (list : Blocklist) (port : Nat) (msg : List U8)
    (reply : Nat → dns.DnsQuery → Prop) : Verdict → Prop
  | .Pass => ¬ (port = 53 ∧ QueryBlocked list msg)
  | .Drop => port = 53 ∧ QueryBlocked list msg
  | .Reply n => port = 53 ∧ ∃ q, dns.DnsQuery.Spec msg q ∧ BlockedBy list q.name.text ∧ reply n.val q

/-- The verdict on the data `data` of a TCP segment to port `port`: a
    ClientHello for a blocked name to port 443 is dropped; anything else
    passes. -/
def TcpVerdict (list : Blocklist) (port : Nat) (data : List U8) : Verdict → Prop
  | .Pass => ¬ (port = 443 ∧ HelloBlocked list data)
  | .Drop => port = 443 ∧ HelloBlocked list data
  | .Reply _ => False

theorem _root_.diomede.tls.ClientHello.Spec.inv {s : List U8} {c : tls.ClientHello} {n : name.Name}
    (h : tls.ClientHello.Spec s c) (hn : c.server_name = some n) : n.Inv := by
  unfold tls.ClientHello.Spec at h
  rw [hn] at h
  rcases hs : tls.serverNameN s with _ | _ | hh <;> rw [hs] at h
  all_goals first | exact h.elim | exact h.2.2.1

/-- **Spec theorem for `hello_blocked`**. -/
@[step]
theorem hello_blocked.spec (s : Untrusted (Slice U8)) (list : Blocklist) (hb : list.Inv) :
    hello_blocked s list ⦃ (b : Bool) => (b = true ↔ HelloBlocked list (s : Slice U8).val) ⦄ := by
  unfold hello_blocked
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨c, n, hc, -⟩
    exact hr c hc
  | Ok c =>
    simp only
    cases hn : c.server_name with
    | none =>
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
      rintro ⟨c', n', hc', hn', -⟩
      have := hr.text_eq hc'
      rw [hn, hn'] at this
      simp at this
    | some n =>
      simp only
      step with name.Name.as_bytes.spec n (hr.inv hn) as ⟨s1, hs1⟩
      step with Blocklist.blocked.spec list hb s1 as ⟨b, hbl⟩
      have hv : vals s1.val = n.text := hs1
      constructor
      · intro h
        exact ⟨c, n, hr, hn, by rw [← hv]; exact hbl.1 h⟩
      · rintro ⟨c', n', hc', hn', hbl'⟩
        have := hr.text_eq hc'
        rw [hn, hn'] at this
        simp only [Option.map_some, Option.some.injEq] at this
        exact hbl.2 (by rw [hv, this]; exact hbl')

/-- **Spec theorem for `tcp_verdict`**. -/
@[step]
theorem tcp_verdict.spec (port : U16) (data : Untrusted (Slice U8)) (list : Blocklist)
    (hb : list.Inv) :
    tcp_verdict port data list ⦃ (v : Verdict) =>
      TcpVerdict list port.val (data : Slice U8).val v ⦄ := by
  unfold tcp_verdict
  split
  · simp only [WP.spec_ok, TcpVerdict]
    rename_i hne
    simp only [bne_iff_ne, ne_eq] at hne
    rintro ⟨h443, -⟩
    exact hne (by scalar_tac)
  rename_i heq
  have h443 : port.val = 443 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq; rw [heq]; simp
  step with hello_blocked.spec data list hb as ⟨b, hbl⟩
  split
  · simp only [WP.spec_ok, TcpVerdict]
    rename_i hbt
    exact ⟨h443, hbl.1 hbt⟩
  · simp only [WP.spec_ok, TcpVerdict]
    rename_i hbf
    rintro ⟨-, h⟩
    exact hbf (hbl.2 h)

/-- **Spec theorem for `udp_ipv4`**. -/
@[step]
theorem udp_ipv4.spec (u : net.udp.Ipv4Udp) (list : Blocklist) (out : Slice U8) (hb : list.Inv) :
    udp_ipv4 u list out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        DnsVerdict list (u.header.dst_port : U16).val (u.payload : Slice U8).val
          (Reply4 u r.2.val) r.1 ⦄ := by
  unfold udp_ipv4
  dsimp only
  split
  · simp only [WP.spec_ok, DnsVerdict]
    rename_i hne
    simp only [bne_iff_ne, ne_eq] at hne
    exact ⟨trivial, fun ⟨h53, _⟩ => hne (by scalar_tac)⟩
  rename_i heq
  have h53 : (u.header.dst_port : U16).val = 53 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq; rw [heq]; simp
  step with dns_answer.spec u.payload list _ hb as ⟨o, answer1, ho⟩
  rcases o with _ | _ | n
  · simp only [WP.spec_ok, DnsVerdict]
    exact ⟨trivial, fun ⟨_, h⟩ => ho h⟩
  · simp only [WP.spec_ok, DnsVerdict]
    obtain ⟨q, hq, hbq, -⟩ := ho
    exact ⟨trivial, h53, q, hq, hbq⟩
  obtain ⟨q, hq, hbq, hn, hle, hans⟩ := ho
  step*
  · exact ⟨o2_post, h53, q, hq, hbq⟩
  · rename_i hm
    rw [hm] at o2_post1
    obtain ⟨-, r, hr, hsrc, hdst, hsp, hdp, hpay⟩ := o2_post1
    refine ⟨o2_post, h53, q, hq, hbq, r, hr, hsrc, hdst, by rw [hsp]; simp, hdp, ?_⟩
    rw [hpay, s_post, ← hans]
    simp [List.slice]

/-- **Spec theorem for `udp_ipv6`**. -/
@[step]
theorem udp_ipv6.spec (u : net.udp.Ipv6Udp) (list : Blocklist) (out : Slice U8) (hb : list.Inv) :
    udp_ipv6 u list out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        DnsVerdict list (u.header.dst_port : U16).val (u.payload : Slice U8).val
          (Reply6 u r.2.val) r.1 ⦄ := by
  unfold udp_ipv6
  dsimp only
  split
  · simp only [WP.spec_ok, DnsVerdict]
    rename_i hne
    simp only [bne_iff_ne, ne_eq] at hne
    exact ⟨trivial, fun ⟨h53, _⟩ => hne (by scalar_tac)⟩
  rename_i heq
  have h53 : (u.header.dst_port : U16).val = 53 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq; rw [heq]; simp
  step with dns_answer.spec u.payload list _ hb as ⟨o, answer1, ho⟩
  rcases o with _ | _ | n
  · simp only [WP.spec_ok, DnsVerdict]
    exact ⟨trivial, fun ⟨_, h⟩ => ho h⟩
  · simp only [WP.spec_ok, DnsVerdict]
    obtain ⟨q, hq, hbq, -⟩ := ho
    exact ⟨trivial, h53, q, hq, hbq⟩
  obtain ⟨q, hq, hbq, hn, hle, hans⟩ := ho
  step*
  · exact ⟨o2_post, h53, q, hq, hbq⟩
  · rename_i hm
    rw [hm] at o2_post1
    obtain ⟨-, r, hr, hsrc, hdst, hsp, hdp, hpay⟩ := o2_post1
    refine ⟨o2_post, h53, q, hq, hbq, r, hr, hsrc, hdst, by rw [hsp]; simp, hdp, ?_⟩
    rw [hpay, s_post, ← hans]
    simp [List.slice]

/-! ## Packets -/

/-- What `classify` does with the packet `p`, writing to `out`, decoding
    `p` in turn as UDP over IPv4, UDP over IPv6, TCP over IPv4 and TCP over
    IPv6: the verdict on the DNS message or TCP data of the first that
    accepts it, or `Pass` if none does. -/
def Classify (list : Blocklist) (p out : List U8) (v : Verdict) : Prop :=
  (∃ u, net.udp.Ipv4Udp.Spec p u ∧
    DnsVerdict list (u.header.dst_port : U16).val (u.payload : Slice U8).val (Reply4 u out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ ∃ u, net.udp.Ipv6Udp.Spec p u ∧
    DnsVerdict list (u.header.dst_port : U16).val (u.payload : Slice U8).val (Reply6 u out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    ∃ t, net.tcp.Ipv4Tcp.Spec p t ∧
      TcpVerdict list (t.header.dst_port : U16).val (t.payload : Slice U8).val v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    (∀ t, ¬ net.tcp.Ipv4Tcp.Spec p t) ∧ ∃ t, net.tcp.Ipv6Tcp.Spec p t ∧
      TcpVerdict list (t.header.dst_port : U16).val (t.payload : Slice U8).val v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    (∀ t, ¬ net.tcp.Ipv4Tcp.Spec p t) ∧ (∀ t, ¬ net.tcp.Ipv6Tcp.Spec p t) ∧ v = .Pass)

/-- **Spec theorem for `classify`**. -/
@[step]
theorem classify.spec (packet : Slice U8) (list : Blocklist) (out : Slice U8) (hb : list.Inv) :
    classify packet list out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧ Classify list packet.val r.2.val r.1 ⦄ := by
  unfold classify
  step as ⟨u, hu⟩
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  rw [hu] at hr
  cases r with
  | Ok iu =>
    apply WP.spec_mono (udp_ipv4.spec iu list out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inl ⟨iu, hr, hv⟩⟩
  | Err _ =>
  simp only
  step as ⟨r1, hr1⟩
  rw [hu] at hr1
  cases r1 with
  | Ok iu =>
    apply WP.spec_mono (udp_ipv6.spec iu list out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inr (Or.inl ⟨hr, iu, hr1, hv⟩)⟩
  | Err _ =>
  simp only
  step as ⟨r2, hr2⟩
  rw [hu] at hr2
  cases r2 with
  | Ok it =>
    simp only
    step with tcp_verdict.spec _ it.payload list hb as ⟨v, hv⟩
    exact Or.inr (Or.inr (Or.inl ⟨hr, hr1, it, hr2, hv⟩))
  | Err _ =>
  simp only
  step as ⟨r3, hr3⟩
  rw [hu] at hr3
  cases r3 with
  | Ok it =>
    simp only
    step with tcp_verdict.spec _ it.payload list hb as ⟨v, hv⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, hr1, hr2, it, hr3, hv⟩)))
  | Err _ =>
    simp only [WP.spec_ok]
    exact ⟨trivial, by unfold Classify; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hr1, hr2, hr3, rfl⟩)))⟩

/-- **Spec theorem for `classify_stream`**: whether the stream starts with a
    ClientHello for a blocked name. -/
@[step]
theorem classify_stream.spec (stream : Slice U8) (list : Blocklist) (hb : list.Inv) :
    classify_stream stream list ⦃ (b : Bool) => (b = true ↔ HelloBlocked list stream.val) ⦄ := by
  unfold classify_stream
  step as ⟨u, hu⟩
  apply WP.spec_mono (hello_blocked.spec u list hb)
  intro b hb'
  rw [hu] at hb'
  exact hb'

end filter
end diomede
