with Super;

generic
   Max : Positive;
package P with SPARK_Mode is
   type Typ is private;
   function Id
     (Source : Typ) return Typ;
private
   type Typ is new Super.Sup (Max);
end P;
