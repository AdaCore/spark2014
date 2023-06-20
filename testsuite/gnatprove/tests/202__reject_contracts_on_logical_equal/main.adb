procedure Main is
   function F (X : Integer; Y : Integer) return Boolean is (X = Y)
     with Ghost,
       Global => null,
       Annotate => (GNATprove, Logical_Equal),
       Pre => X = 0,
       Post => (if F'Result then Y = 0);
   function G (X : Integer; Y : Integer) return Boolean is (X = Y)
     with Ghost,
       Global => null,
       Annotate => (GNATprove, Logical_Equal),
       Contract_Cases => (X = 0 => (if G'Result then Y = 0),
                        others => (if G'Result then Y /= 0));
begin
   null;
end Main;
