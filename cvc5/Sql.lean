inductive TimePart where
  | Year : TimePart
  | Month : TimePart
  | Day : TimePart
  | Hour : TimePart
  | Minute : TimePart
  | Second : TimePart

inductive Basetype where
  | bigint : Basetype
  | bigserial : Basetype
  | bit (size: Nat) : Basetype
  | bitVarying (size: Nat) : Basetype
  | boolean : Basetype
  | box : Basetype
  | bytea : Basetype
  | character (size: Nat) : Basetype
  | characterVarying (size: Nat) : Basetype
  | cidr : Basetype
  | circle : Basetype
  | date : Basetype
  | doublePrecision : Basetype
  | inet : Basetype
  | integer : Basetype
  | interval (fields : List TimePart) (precision: Nat) : Basetype
  | json : Basetype
  | jsonb : Basetype
  | line : Basetype
  | lseg : Basetype
  | macaddr : Basetype
  | macaddr8 : Basetype
  | money : Basetype
  | numeric (precision significand: Nat) : Basetype
  | path : Basetype
  | pg_lsn : Basetype
  | pg_snapshot : Basetype
  | point : Basetype
  | polygon : Basetype
  | real : Basetype
  | smallint : Basetype
  | smallserial : Basetype
  | serial : Basetype
  | text : Basetype
  | timeWithoutTimeZone (precision : Nat) : Basetype
  | timeWithTimeZone (precision : Nat): Basetype
  | timestampWithoutTimeZone (precision : Nat): Basetype
  | timestampWithTimeZone (precision : Nat) : Basetype
  | tsquery : Basetype
  | tsvector : Basetype
  | txid_snapshot : Basetype
  | uuid : Basetype
  | xml : Basetype

inductive Datatype where
  | datatype(basetype : Basetype) (isNull : Bool) : Datatype
