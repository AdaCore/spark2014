procedure Inout1 (A : Integer; Z : out Integer) with
  Depends => (Z => A)
is
   type T is record
      C : Integer;
   end record;
   --  A type which is neither by-copy nor by-reference

   procedure Try (X : Integer; By_Unspecified : in out T) with
     Import,
     Global => null,
     Always_Terminates => True,
     Exceptional_Cases => (Program_Error => X > 0);

   procedure Test (Proxy : in out T) is
   begin
      Try (A, By_Unspecified => Proxy);
      Z := Proxy.C;
   exception
      when Program_Error =>
         Z := Proxy.C; --  @INITIALIZED:CHECK
   end Test;

   Proxy : T := (C => 0);

begin
   Test (Proxy);
end Inout1;
