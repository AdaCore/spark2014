package body Inside_Out is

   procedure Body_Create (X : out T);

   procedure Body_Update (X : in out T);

   function Body_Get (X : T) return Integer;

   procedure Body_Create (X : out T) is  --  @INVARIANT_CHECK:NONE
   begin
      Create (X);  --  @INVARIANT_CHECK:NONE
   end Body_Create;

   procedure Body_Update (X : in out T) is  --  @INVARIANT_CHECK:NONE
   begin
      Update (X);  --  @INVARIANT_CHECK:FAIL
   end Body_Update;

   function Body_Get (X : T) return Integer is
      (Get (X));   --  @INVARIANT_CHECK:FAIL

   procedure Priv_Create (X : out T) is  --  @INVARIANT_CHECK:NONE
   begin
      X := 1;  --  @INVARIANT_CHECK:NONE
   end Priv_Create;

   procedure Priv_Update (X : in out T) is  --  @INVARIANT_CHECK:NONE
   begin
      if X /= T'First then
         X := abs (X);  --  @INVARIANT_CHECK:NONE
      end if;
   end Priv_Update;

   function Priv_Get (X : T) return Integer is (Integer (X));

   type Mode_T is (Rec, Bod, Prv);
   Mode : Mode_T := Prv;

   procedure Create (X : out T) is  --  @INVARIANT_CHECK:FAIL
   begin
      case Mode is
         when Rec =>
            Create (X);  --  @INVARIANT_CHECK:NONE
         when Bod =>
            Body_Create (X);  --  @INVARIANT_CHECK:NONE
         when Prv =>
            Priv_Create (X);  --  @INVARIANT_CHECK:NONE
      end case;
   end Create;

   procedure Update (X : in out T) is  --  @INVARIANT_CHECK:FAIL
   begin
      X := 0;
      case Mode is
         when Rec =>
            Update (X);  --  @INVARIANT_CHECK:FAIL
         when Bod =>
            Body_Update (X);  --  @INVARIANT_CHECK:NONE
         when Prv =>
            Priv_Update (X);  --  @INVARIANT_CHECK:NONE
      end case;
   end Update;

   function Get (X : T) return Integer is
   begin
      case Mode is
         when Rec =>
            return Get (X);  --  @INVARIANT_CHECK:NONE
         when Bod =>
            return Body_Get (X);  --  @INVARIANT_CHECK:NONE
         when Prv =>
            return Priv_Get (X);  --  @INVARIANT_CHECK:NONE
      end case;
   end Get;

end Inside_Out;
