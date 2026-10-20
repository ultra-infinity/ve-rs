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

/-! ## Constants and determinism -/

@[simp, scalar_tac_simps] theorem dns_PORT_val : dns.PORT.val = 53 := by simp [dns.PORT]
@[simp, scalar_tac_simps] theorem tls_PORT_val : tls.PORT.val = 443 := by simp [tls.PORT]
@[simp, scalar_tac_simps] theorem DOT_PORT_val : DOT_PORT.val = 853 := by simp [DOT_PORT]
@[simp, scalar_tac_simps] theorem RST_ACK_val : RST_ACK.val = 20 := by simp [RST_ACK]
theorem RST_ACK_eq : RST_ACK = 20#u8 := by unfold RST_ACK; rfl
@[simp, scalar_tac_simps] theorem dns_NOERROR_val : dns.NOERROR.val = 0 := by simp [dns.NOERROR]
@[simp, scalar_tac_simps] theorem dns_TYPE_HTTPS_val : dns.TYPE_HTTPS.val = 65 := by
  simp [dns.TYPE_HTTPS]
@[simp, scalar_tac_simps] theorem dns_TYPE_SVCB_val : dns.TYPE_SVCB.val = 64 := by
  simp [dns.TYPE_SVCB]

/-- A query's type is determined by the message. -/
theorem _root_.diomede.dns.DnsQuery.Spec.qtype_eq {m : List U8} {q q' : dns.DnsQuery}
    (h : dns.DnsQuery.Spec m q) (h' : dns.DnsQuery.Spec m q') : q.qtype = q'.qtype := by
  obtain ⟨-, -, -, -, -, -, ls, k, hf, -, -, -, -, ht, -⟩ := h
  obtain ⟨-, -, -, -, -, -, ls', k', hf', -, -, -, -, ht', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := hf.unique hf'
  exact (UScalar.eq_equiv _ _).mpr (by rw [ht, ht'])

theorem _root_.diomede.tls.ClientHello.Spec.inv {s : List U8} {c : tls.ClientHello} {n : name.Name}
    (h : tls.ClientHello.Spec s c) (hn : c.server_name = some n) : n.Inv := by
  unfold tls.ClientHello.Spec at h
  rw [hn] at h
  rcases hs : tls.serverNameN s with _ | _ | hh <;> rw [hs] at h
  all_goals first | exact h.elim | exact h.2.2.1

/-! ## DNS -/

/-- `qtype` is HTTPS (65) or SVCB (64): the records that carry Encrypted
    ClientHello keys and HTTP/3 hints. -/
def HttpsType (qtype : Nat) : Prop := qtype = 65 ∨ qtype = 64

/-- `msg` is the query `q`, to be answered with response code `rcode`:
    NXDOMAIN (3) if its name is blocked; else NOERROR (0), with no records,
    if it asks for HTTPS or SVCB records and the policy strips them. -/
def Answer (list : Blocklist) (policy : Policy) (msg : List U8) (q : dns.DnsQuery)
    (rcode : Nat) : Prop :=
  dns.DnsQuery.Spec msg q ∧
    ((BlockedBy list q.name.text ∧ rcode = 3) ∨
      (¬ BlockedBy list q.name.text ∧ policy.strip_https_rr = true ∧ HttpsType q.qtype.val ∧
        rcode = 0))

/-- `msg` is a query the filter answers. -/
def Answered (list : Blocklist) (policy : Policy) (msg : List U8) : Prop :=
  ∃ q rcode, Answer list policy msg q rcode

/-- **Spec theorem for `https_type`**. -/
@[step]
theorem https_type.spec (qtype : U16) :
    https_type qtype ⦃ (b : Bool) => (b = true ↔ HttpsType qtype.val) ⦄ := by
  unfold https_type HttpsType
  split
  · simp only [WP.spec_ok, true_iff]; left; scalar_tac
  · simp only [WP.spec_ok, decide_eq_true_eq]
    constructor
    · intro h; right; scalar_tac
    · rintro (h | h)
      · exfalso; rename_i hne; exact hne (by scalar_tac)
      · scalar_tac

/-- **Spec theorem for `dns_answer`**: whether `msg` is a query to answer
    and, if so, its answer in `answer`, if it fits. -/
@[step]
theorem dns_answer.spec (msg : Untrusted (Slice U8)) (list : Blocklist) (policy : Policy)
    (answer : Array U8 512#usize) (hb : list.Inv) :
    dns_answer msg list policy answer ⦃ (r : Option (Option Usize) × Array U8 512#usize) =>
      match r.1 with
      | none => ¬ Answered list policy (msg : Slice U8).val
      | some o => ∃ q rcode, Answer list policy (msg : Slice U8).val q rcode ∧
          match o with
          | none => True
          | some n => n.val = 12 + q.question_len.val ∧ n.val ≤ 512 ∧
              (r.2.val.take n.val).map (·.val) = dns.answerN (msg : Slice U8).val q rcode ⦄ := by
  unfold dns_answer
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp only [WP.spec_ok]
    rintro ⟨q, rc, hq, -⟩
    exact hr q hq
  | Ok q =>
    obtain ⟨hm, hq⟩ := hr
    have hinv : q.query.name.Inv := hq.2.2.2.2.2.2.choose_spec.choose_spec.2.2.2.1
    simp only
    step with name.Name.as_bytes.spec q.query.name hinv as ⟨s, hs⟩
    step with Blocklist.blocked.spec list hb s as ⟨b, hbl⟩
    have hv : vals s.val = q.query.name.text := hs
    split
    · rename_i hbt
      have hB : BlockedBy list q.query.name.text := by rw [← hv]; exact hbl.1 hbt
      step*
      refine ⟨q.query, 3, ⟨hq, Or.inl ⟨hB, rfl⟩⟩, ?_⟩
      rcases o with _ | n
      · trivial
      · obtain ⟨h1, hle, h2, h3, -⟩ := o_post
        refine ⟨h1, by simp_all [Slice.length], ?_⟩
        rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by simp_all [Slice.length]), ← hm, h3,
          dns.NXDOMAIN_val]
    rename_i hbf
    have hnB : ¬ BlockedBy list q.query.name.text := fun h => hbf (hbl.2 (by rw [hv]; exact h))
    have hno : ∀ q' rc, Answer list policy msg.val q' rc →
        (policy.strip_https_rr = true ∧ HttpsType q.query.qtype.val ∧ rc = 0) := by
      rintro q' rc ⟨hq', h | ⟨-, hs', ht', hr'⟩⟩
      · rw [hq'.text_eq hq] at h; exact absurd h.1 hnB
      · rw [hq'.qtype_eq hq] at ht'; exact ⟨hs', ht', hr'⟩
    split
    · rename_i hstrip
      step with https_type.spec q.query.qtype as ⟨b1, hb1⟩
      split
      · rename_i hbt1
        step*
        refine ⟨q.query, 0, ⟨hq, Or.inr ⟨hnB, hstrip, hb1.1 hbt1, rfl⟩⟩, ?_⟩
        rcases o with _ | n
        · trivial
        · obtain ⟨h1, hle, h2, h3, -⟩ := o_post
          refine ⟨h1, by simp_all [Slice.length], ?_⟩
          rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by simp_all [Slice.length]), ← hm, h3,
            dns_NOERROR_val]
      · rename_i hbf1
        simp only [WP.spec_ok]
        rintro ⟨q', rc, ha⟩
        exact hbf1 (hb1.2 (hno q' rc ha).2.1)
    · rename_i hnstrip
      simp only [WP.spec_ok]
      rintro ⟨q', rc, ha⟩
      exact hnstrip (hno q' rc ha).1

/-! ## UDP -/

/-- UDP to `port` (other than DNS) is dropped by the policy: QUIC (443) or
    DNS over QUIC (853). -/
def UdpDropped (policy : Policy) (port : Nat) : Prop :=
  (port = 443 ∧ policy.block_quic = true) ∨ (port = 853 ∧ policy.block_dot = true)

/-- The reply `out[..n]` to the query `q` in the datagram `u`, over IPv4: from
    the server the query was sent to, back to the client, carrying the answer
    with response code `rcode`. -/
def Reply4 (u : net.udp.Ipv4Udp) (out : List U8) (n : Nat) (q : dns.DnsQuery) (rcode : Nat) :
    Prop :=
  ∃ r : net.udp.Ipv4Udp, net.udp.Ipv4Udp.Spec (out.take n) r ∧
    r.ip.header.src = u.ip.header.dst ∧ r.ip.header.dst = u.ip.header.src ∧
    (r.header.src_port : U16).val = 53 ∧ r.header.dst_port = u.header.src_port ∧
    (r.payload : Slice U8).val.map (·.val) = dns.answerN (u.payload : Slice U8).val q rcode

/-- The reply `out[..n]` to the query `q` in the datagram `u`, over IPv6. -/
def Reply6 (u : net.udp.Ipv6Udp) (out : List U8) (n : Nat) (q : dns.DnsQuery) (rcode : Nat) :
    Prop :=
  ∃ r : net.udp.Ipv6Udp, net.udp.Ipv6Udp.Spec (out.take n) r ∧
    r.ip.header.src = u.ip.header.dst ∧ r.ip.header.dst = u.ip.header.src ∧
    (r.header.src_port : U16).val = 53 ∧ r.header.dst_port = u.header.src_port ∧
    (r.payload : Slice U8).val.map (·.val) = dns.answerN (u.payload : Slice U8).val q rcode

/-- The verdict on a UDP datagram to `port` carrying `msg`: a query to port
    53 the filter answers gets an answer (`reply n q rcode` describes it),
    or is dropped if the answer does not fit; QUIC and DNS over QUIC are
    dropped as the policy says; anything else passes. -/
def UdpVerdict (list : Blocklist) (policy : Policy) (port : Nat) (msg : List U8)
    (reply : Nat → dns.DnsQuery → Nat → Prop) : Verdict → Prop
  | .Pass => ¬ (port = 53 ∧ Answered list policy msg) ∧ ¬ UdpDropped policy port
  | .Drop => (port = 53 ∧ Answered list policy msg) ∨ UdpDropped policy port
  | .Reply n => port = 53 ∧ ∃ q rcode, Answer list policy msg q rcode ∧ reply n.val q rcode
  | .Reset _ => False

/-- **Spec theorem for `udp_dropped`**. -/
@[step]
theorem udp_dropped.spec (policy : Policy) (port : U16) :
    udp_dropped policy port ⦃ (b : Bool) => (b = true ↔ UdpDropped policy port.val) ⦄ := by
  unfold udp_dropped UdpDropped
  split
  · simp only [WP.spec_ok]
    have : port.val = 443 := by scalar_tac
    simp [this]
  split
  · simp only [WP.spec_ok]
    have : port.val = 853 := by scalar_tac
    simp [this]
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h1 h2
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact h1 (by scalar_tac)
    · exact h2 (by scalar_tac)

theorem not_dropped_53 (policy : Policy) : ¬ UdpDropped policy 53 := by
  simp [UdpDropped]

/-- **Spec theorem for `udp_ipv4`**. -/
@[step]
theorem udp_ipv4.spec (u : net.udp.Ipv4Udp) (list : Blocklist) (policy : Policy) (out : Slice U8)
    (hb : list.Inv) :
    udp_ipv4 u list policy out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        UdpVerdict list policy (u.header.dst_port : U16).val (u.payload : Slice U8).val
          (Reply4 u r.2.val) r.1 ⦄ := by
  unfold udp_ipv4
  dsimp only
  split
  · rename_i hne
    have h53 : (u.header.dst_port : U16).val ≠ 53 := by
      simp only [bne_iff_ne, ne_eq] at hne; exact fun h => hne (by scalar_tac)
    step with udp_dropped.spec policy u.header.dst_port as ⟨b, hbd⟩
    split
    · simp only [WP.spec_ok, UdpVerdict]
      rename_i hbt
      exact ⟨trivial, Or.inr (hbd.1 hbt)⟩
    · simp only [WP.spec_ok, UdpVerdict]
      rename_i hbf
      exact ⟨trivial, fun ⟨h, _⟩ => h53 h, fun h => hbf (hbd.2 h)⟩
  rename_i heq
  have h53 : (u.header.dst_port : U16).val = 53 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq; rw [heq]; simp
  step with dns_answer.spec u.payload list policy _ hb as ⟨o, answer1, ho⟩
  rcases o with _ | _ | n
  · simp only [WP.spec_ok, UdpVerdict]
    exact ⟨trivial, fun ⟨_, h⟩ => ho h, by rw [h53]; exact not_dropped_53 policy⟩
  · simp only [WP.spec_ok, UdpVerdict]
    obtain ⟨q, rc, ha, -⟩ := ho
    exact ⟨trivial, Or.inl ⟨h53, q, rc, ha⟩⟩
  obtain ⟨q, rc, ha, hn, hle, hans⟩ := ho
  step*
  · exact ⟨o2_post, by simp only [UdpVerdict]; exact Or.inl ⟨h53, q, rc, ha⟩⟩
  · rename_i hm
    rw [hm] at o2_post1
    obtain ⟨-, r, hr, hsrc, hdst, hsp, hdp, hpay⟩ := o2_post1
    refine ⟨o2_post, h53, q, rc, ha, r, hr, hsrc, hdst, by rw [hsp]; simp, hdp, ?_⟩
    rw [hpay, s_post, ← hans]
    simp [List.slice]

/-- **Spec theorem for `udp_ipv6`**. -/
@[step]
theorem udp_ipv6.spec (u : net.udp.Ipv6Udp) (list : Blocklist) (policy : Policy) (out : Slice U8)
    (hb : list.Inv) :
    udp_ipv6 u list policy out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        UdpVerdict list policy (u.header.dst_port : U16).val (u.payload : Slice U8).val
          (Reply6 u r.2.val) r.1 ⦄ := by
  unfold udp_ipv6
  dsimp only
  split
  · rename_i hne
    have h53 : (u.header.dst_port : U16).val ≠ 53 := by
      simp only [bne_iff_ne, ne_eq] at hne; exact fun h => hne (by scalar_tac)
    step with udp_dropped.spec policy u.header.dst_port as ⟨b, hbd⟩
    split
    · simp only [WP.spec_ok, UdpVerdict]
      rename_i hbt
      exact ⟨trivial, Or.inr (hbd.1 hbt)⟩
    · simp only [WP.spec_ok, UdpVerdict]
      rename_i hbf
      exact ⟨trivial, fun ⟨h, _⟩ => h53 h, fun h => hbf (hbd.2 h)⟩
  rename_i heq
  have h53 : (u.header.dst_port : U16).val = 53 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq; rw [heq]; simp
  step with dns_answer.spec u.payload list policy _ hb as ⟨o, answer1, ho⟩
  rcases o with _ | _ | n
  · simp only [WP.spec_ok, UdpVerdict]
    exact ⟨trivial, fun ⟨_, h⟩ => ho h, by rw [h53]; exact not_dropped_53 policy⟩
  · simp only [WP.spec_ok, UdpVerdict]
    obtain ⟨q, rc, ha, -⟩ := ho
    exact ⟨trivial, Or.inl ⟨h53, q, rc, ha⟩⟩
  obtain ⟨q, rc, ha, hn, hle, hans⟩ := ho
  step*
  · exact ⟨o2_post, by simp only [UdpVerdict]; exact Or.inl ⟨h53, q, rc, ha⟩⟩
  · rename_i hm
    rw [hm] at o2_post1
    obtain ⟨-, r, hr, hsrc, hdst, hsp, hdp, hpay⟩ := o2_post1
    refine ⟨o2_post, h53, q, rc, ha, r, hr, hsrc, hdst, by rw [hsp]; simp, hdp, ?_⟩
    rw [hpay, s_post, ← hans]
    simp [List.slice]

/-! ## TCP -/

/-- A TCP segment to `port` carrying `data` is reset: a ClientHello for a
    blocked name to port 443, or DNS over TLS (port 853) if the policy says
    so. -/
def TcpReset (list : Blocklist) (policy : Policy) (port : Nat) (data : List U8) : Prop :=
  (port = 443 ∧ HelloBlocked list data) ∨ (port = 853 ∧ policy.block_dot = true)

/-- The acknowledgment number of the reset answering the segment with
    header `h` and `len` bytes of data: past its data and SYN. -/
def resetAck (h : net.tcp.TcpHeader) (len : Nat) : Nat :=
  ((h.seq : U32).val + len + (h.flags : U8).val / 2 % 2) % 4294967296

/-- The reset `out[..n]` answering the segment `t` (with `len` bytes of
    data) over IPv4: from the server back to the client, with the ports
    swapped, the segment's acknowledgment number as its sequence number,
    `resetAck` as its acknowledgment number, and RST and ACK. -/
def Reset4 (t : net.tcp.Ipv4Tcp) (len : Nat) (out : List U8) (n : Nat) : Prop :=
  ∃ r : net.tcp.Ipv4Tcp, net.tcp.Ipv4Tcp.Spec (out.take n) r ∧
    r.ip.header.src = t.ip.header.dst ∧ r.ip.header.dst = t.ip.header.src ∧
    ∃ a : U32, a.val = resetAck t.header len ∧ (r.payload : Slice U8).val = [] ∧
      r.header = net.tcp.bareHeader t.header.dst_port t.header.src_port t.header.ack a 20#u8
        r.header.checksum

/-- The reset `out[..n]` answering the segment `t` over IPv6. -/
def Reset6 (t : net.tcp.Ipv6Tcp) (len : Nat) (out : List U8) (n : Nat) : Prop :=
  ∃ r : net.tcp.Ipv6Tcp, net.tcp.Ipv6Tcp.Spec (out.take n) r ∧
    r.ip.header.src = t.ip.header.dst ∧ r.ip.header.dst = t.ip.header.src ∧
    ∃ a : U32, a.val = resetAck t.header len ∧ (r.payload : Slice U8).val = [] ∧
      r.header = net.tcp.bareHeader t.header.dst_port t.header.src_port t.header.ack a 20#u8
        r.header.checksum

/-- The verdict on a TCP segment to `port` carrying `data`: reset (`reset n`
    describes it, and it is dropped if the reset does not fit) if
    `TcpReset`, else passed. -/
def TcpVerdict (list : Blocklist) (policy : Policy) (port : Nat) (data : List U8)
    (reset : Nat → Prop) : Verdict → Prop
  | .Pass => ¬ TcpReset list policy port data
  | .Drop => TcpReset list policy port data
  | .Reset n => TcpReset list policy port data ∧ reset n.val
  | .Reply _ => False

/-- **Spec theorem for `hello_blocked`**. -/
@[step]
theorem hello_blocked.spec (s : Slice U8) (list : Blocklist) (hb : list.Inv) :
    hello_blocked s list ⦃ (b : Bool) => (b = true ↔ HelloBlocked list s.val) ⦄ := by
  unfold hello_blocked
  step as ⟨u, hu⟩
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  rw [hu] at hr
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

/-- **Spec theorem for `<Data as Validate<&[u8]>>::validate`**: the bytes,
    as they are. -/
@[step]
theorem Data.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec (input : Slice U8) :
    Data.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Data ValidationError) => r = .Ok input ⦄ := by
  unfold Data.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  simp

/-- **Spec theorem for `tcp_reset`**. -/
@[step]
theorem tcp_reset.spec (port : U16) (data : Slice U8) (list : Blocklist) (policy : Policy)
    (hb : list.Inv) :
    tcp_reset port data list policy ⦃ (b : Bool) =>
      (b = true ↔ TcpReset list policy port.val data.val) ⦄ := by
  unfold tcp_reset TcpReset
  split
  · have h443 : port.val = 443 := by scalar_tac
    apply WP.spec_mono (hello_blocked.spec data list hb)
    intro b hbl
    simp [h443, hbl]
  split
  · simp only [WP.spec_ok]
    have : port.val = 853 := by scalar_tac
    simp [this]
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h1 h2
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact h1 (by scalar_tac)
    · exact h2 (by scalar_tac)

/-- **Spec theorem for `reset_numbers`**. -/
@[step]
theorem reset_numbers.spec (h : net.tcp.TcpHeader) (len : Usize) :
    reset_numbers h len ⦃ (r : U32 × U32) => r.1 = h.ack ∧ r.2.val = resetAck h len.val ⦄ := by
  unfold reset_numbers resetAck
  step*
  simp only [ack_post, i5_post, syn_post, i4_post, core.num.U32.wrapping_add_val_eq,
    UScalar.cast_val_eq, UScalarTy.numBits, i2_post, i1_post]
  have := (h.flags : U8).hBounds
  simp only [UScalarTy.U8_numBits_eq] at this
  have hs : U32.size = 4294967296 := by simp [U32.size, U32.numBits]
  simp only [UScalar.size_UScalarTyU32, hs]
  omega

/-- **Spec theorem for `tcp_ipv4`**. -/
@[step]
theorem tcp_ipv4.spec (t : net.tcp.Ipv4Tcp) (list : Blocklist) (policy : Policy) (out : Slice U8)
    (hb : list.Inv) :
    tcp_ipv4 t list policy out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        TcpVerdict list policy (t.header.dst_port : U16).val (t.payload : Slice U8).val
          (Reset4 t (t.payload : Slice U8).length r.2.val) r.1 ⦄ := by
  unfold tcp_ipv4
  simp only [Untrusted.validate_eq]
  step*
  all_goals have hd : d = t.payload := (by
    have h1 := ‹r = core.result.Result.Ok d›
    rw [r_post] at h1
    injection h1 with h1
    exact h1.symm)
  all_goals subst hd
  · exact ⟨o_post, b_post.1 ‹_›⟩
  · have hn : o = some n := ‹_›
    rw [hn] at o_post1
    obtain ⟨-, r, hr, hsrc, hdst, hhdr, hpay⟩ := o_post1
    refine ⟨o_post, b_post.1 ‹_›, r, hr, hsrc, hdst, ack, ?_, hpay, ?_⟩
    · rw [seq_post1, Slice.len_val]
    · rw [hhdr, seq_post, RST_ACK_eq]; rfl
  · exact fun h => ‹¬b = true› (b_post.2 h)

/-- **Spec theorem for `tcp_ipv6`**. -/
@[step]
theorem tcp_ipv6.spec (t : net.tcp.Ipv6Tcp) (list : Blocklist) (policy : Policy) (out : Slice U8)
    (hb : list.Inv) :
    tcp_ipv6 t list policy out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧
        TcpVerdict list policy (t.header.dst_port : U16).val (t.payload : Slice U8).val
          (Reset6 t (t.payload : Slice U8).length r.2.val) r.1 ⦄ := by
  unfold tcp_ipv6
  simp only [Untrusted.validate_eq]
  step*
  all_goals have hd : d = t.payload := (by
    have h1 := ‹r = core.result.Result.Ok d›
    rw [r_post] at h1
    injection h1 with h1
    exact h1.symm)
  all_goals subst hd
  · exact ⟨o_post, b_post.1 ‹_›⟩
  · have hn : o = some n := ‹_›
    rw [hn] at o_post1
    obtain ⟨-, r, hr, hsrc, hdst, hhdr, hpay⟩ := o_post1
    refine ⟨o_post, b_post.1 ‹_›, r, hr, hsrc, hdst, ack, ?_, hpay, ?_⟩
    · rw [seq_post1, Slice.len_val]
    · rw [hhdr, seq_post, RST_ACK_eq]; rfl
  · exact fun h => ‹¬b = true› (b_post.2 h)

/-! ## Packets -/

/-- What `classify` does with the packet `p` under `policy`, writing to
    `out`, decoding `p` in turn as UDP over IPv4, UDP over IPv6, TCP over
    IPv4 and TCP over IPv6: the verdict on the datagram or segment of the
    first that accepts it, or `Pass` if none does. -/
def Classify (list : Blocklist) (policy : Policy) (p out : List U8) (v : Verdict) : Prop :=
  (∃ u, net.udp.Ipv4Udp.Spec p u ∧
    UdpVerdict list policy (u.header.dst_port : U16).val (u.payload : Slice U8).val
      (Reply4 u out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ ∃ u, net.udp.Ipv6Udp.Spec p u ∧
    UdpVerdict list policy (u.header.dst_port : U16).val (u.payload : Slice U8).val
      (Reply6 u out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    ∃ t, net.tcp.Ipv4Tcp.Spec p t ∧
      TcpVerdict list policy (t.header.dst_port : U16).val (t.payload : Slice U8).val
        (Reset4 t (t.payload : Slice U8).length out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    (∀ t, ¬ net.tcp.Ipv4Tcp.Spec p t) ∧ ∃ t, net.tcp.Ipv6Tcp.Spec p t ∧
      TcpVerdict list policy (t.header.dst_port : U16).val (t.payload : Slice U8).val
        (Reset6 t (t.payload : Slice U8).length out) v) ∨
  ((∀ u, ¬ net.udp.Ipv4Udp.Spec p u) ∧ (∀ u, ¬ net.udp.Ipv6Udp.Spec p u) ∧
    (∀ t, ¬ net.tcp.Ipv4Tcp.Spec p t) ∧ (∀ t, ¬ net.tcp.Ipv6Tcp.Spec p t) ∧ v = .Pass)

/-- **Spec theorem for `classify`**. -/
@[step]
theorem classify.spec (packet : Slice U8) (list : Blocklist) (policy : Policy) (out : Slice U8)
    (hb : list.Inv) :
    classify packet list policy out ⦃ (r : Verdict × Slice U8) =>
      r.2.length = out.length ∧ Classify list policy packet.val r.2.val r.1 ⦄ := by
  unfold classify
  step as ⟨u, hu⟩
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  rw [hu] at hr
  cases r with
  | Ok iu =>
    apply WP.spec_mono (udp_ipv4.spec iu list policy out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inl ⟨iu, hr, hv⟩⟩
  | Err _ =>
  simp only
  step as ⟨r1, hr1⟩
  rw [hu] at hr1
  cases r1 with
  | Ok iu =>
    apply WP.spec_mono (udp_ipv6.spec iu list policy out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inr (Or.inl ⟨hr, iu, hr1, hv⟩)⟩
  | Err _ =>
  simp only
  step as ⟨r2, hr2⟩
  rw [hu] at hr2
  cases r2 with
  | Ok it =>
    apply WP.spec_mono (tcp_ipv4.spec it list policy out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inr (Or.inr (Or.inl ⟨hr, hr1, it, hr2, hv⟩))⟩
  | Err _ =>
  simp only
  step as ⟨r3, hr3⟩
  rw [hu] at hr3
  cases r3 with
  | Ok it =>
    apply WP.spec_mono (tcp_ipv6.spec it list policy out hb)
    rintro ⟨v, out'⟩ ⟨hl, hv⟩
    exact ⟨hl, by unfold Classify; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, hr1, hr2, it, hr3, hv⟩)))⟩
  | Err _ =>
    simp only [WP.spec_ok]
    exact ⟨trivial, by unfold Classify; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hr1, hr2, hr3, rfl⟩)))⟩

/-- **Spec theorem for `classify_stream`**: whether the stream starts with a
    ClientHello for a blocked name. -/
@[step]
theorem classify_stream.spec (stream : Slice U8) (list : Blocklist) (hb : list.Inv) :
    classify_stream stream list ⦃ (b : Bool) => (b = true ↔ HelloBlocked list stream.val) ⦄ := by
  unfold classify_stream
  exact hello_blocked.spec stream list hb

end filter
end diomede
