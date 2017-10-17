package Case_Assign is
  type Oper is (Incr, Decr, Double);
  procedure Assign (X : out Integer; Y : in Integer; Op : in Oper);
end Case_Assign;
