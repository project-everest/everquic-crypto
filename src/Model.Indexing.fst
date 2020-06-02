module Model.Indexing

module G = FStar.Ghost

let id = if model then ha & ea & ca else unit

let is_honest i = false
// Shit, the erasure issue with eqtype is back
let id_ginfo i : GTot (ha & ea & ca) = if model then i else admit()
//  let (u,v,w) = i <: galg in (G.reveal u, G.reveal v, G.reveal w)
let id_info i = if model then i else admit()

let ae_id = if model then ea else unit
let is_ae_honest i = false
let ae_id_ginfo i = if model then i else admit()
let ae_id_info i = if model then i else admit()

let pne_id = if model then ca else unit
let is_pne_honest i = false
let pne_id_ginfo i = if model then i else admit()
let pne_id_info i = if model then i else admit()
