with Interfaces; use Interfaces;
package Bug1
  with SPARK_Mode => On
is
   type Seq is array (Natural range <>) of Integer;
   subtype Seq_N is Seq (0 .. 3);
   Zero_Seq_N : constant Seq_N := (others => 0);

   procedure P (C :    out Seq;
                M : in     Seq)
     with Global => null,
          Pre    => M'First = 0 and
                    C'First = 0 and
                    C'Last  = M'Last and
                    M'Last >= 3 and
                    M (0 .. 3) = Zero_Seq_N;
end Bug1;
