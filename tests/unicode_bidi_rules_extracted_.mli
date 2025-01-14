
type bidi_class =
| WS
| S
| RLO
| RLI
| RLE
| R
| PDI
| PDF
| ON
| NSM
| LRO
| LRI
| LRE
| L
| FSI
| ET
| ES
| EN
| CS
| BN
| B
| AN
| AL

val rule_w1 : bidi_class list -> bidi_class -> bidi_class list

val next_is_al : bidi_class -> bool -> bool

val rule_w2 : bidi_class list -> bool -> bidi_class list

val rule_w3 : bidi_class list -> bidi_class list

val rule_w4 : bidi_class list -> bidi_class -> bidi_class list

val w5_before_en : bidi_class list -> bool

val rule_w5 : bidi_class list -> bool -> bidi_class list

val rule_w6 : bidi_class list -> bidi_class list

val rule_w7 : bidi_class list -> bool -> bidi_class list

val is_ni : bidi_class -> bool

val is_strong : bidi_class -> bool

val n1_next_strong : bidi_class list -> bidi_class -> bidi_class

val rule_n1 : bidi_class list -> bidi_class -> bidi_class -> bidi_class list

val rule_n2 : bidi_class list -> bidi_class -> bidi_class list
