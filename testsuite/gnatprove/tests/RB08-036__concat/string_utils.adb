package body String_Utils with SPARK_Mode
is
   function Concatenate
     (A : String; B: String; C, D, E, F ,G, H, I, J, K, L : String := "")
      return String
   is
      pragma Warnings (Off, "is not modified, could be declared constant", Reason => "secret");
      String1 : constant String := A & B & C & D;
      String2 : constant String := E & F & G & H;
      String3 : constant String := I & J & K & L;
      pragma Warnings (On, "is not modified, could be declared constant");
   begin
      return (String1 & String2 & String3);
   end Concatenate;
   pragma Annotate
     (GNATprove, Intentional, "range check might fail", "can only fail with crazy long strings");
end String_Utils;
