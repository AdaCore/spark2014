with Types; use Types;

package body Quantifiers with
  SPARK_Mode
is
   function All_Zero return Array_10_Integer_32 with
     Post => (for all J in Index_10 => All_Zero'Result(J) = 0) is
   begin
      return Array_10_Integer_32'(others => 0);
   end All_Zero;

   procedure Previous_Seen (X : Array_10_Integer_32; Y : Index_10) is
   begin
      pragma Assume (for all J in Index_10 =>
                       (if X(J) = 0 then
                          (for some K in Index_10 => Property (X(K), J))));
      pragma Assert (if X = All_Zero then
                       (for all J in Index_10 =>
                          (for some K in Index_10 => Property (X(K), J))));
   end Previous_Seen;

   procedure Not_For_Some (X : Array_10_Integer_32) is
   begin
      pragma Assume (not (for some J in X'Range => Property (X(J), J)));
      pragma Assert (not (for all J in X'Range => Property (X(J), J)));
   end Not_For_Some;

end Quantifiers;
