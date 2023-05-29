procedure Main with SPARK_Mode is

   type Option (B : Boolean := False) is record
      case B is
         when True =>
            V : Integer;
         when False =>
            null;
      end case;
   end record;

   Constrained : exception;

   procedure Store (V : Integer; O : out Option) with
     Post => O.B and O.V = V,
     Exceptional_Cases => (Constrained => O'Constrained'Old and then not O.B'Old);

   procedure Store (V : Integer; O : out Option) is
   begin
      if O.B then
         O.V := V;
      elsif O'Constrained then
         raise Constrained;
      else
         O := (B => True, V => V);
      end if;
   end Store;

   procedure Call_Store (V : Integer; O : out Option) with
     Post => (if not O'Constrained then O.B and then O.V = V);

   procedure Call_Store (V : Integer; O : out Option) is
   begin
      Store (V, O);
   exception
      when Constrained =>
         pragma Assert (O'Constrained);
         pragma Assert (not O.B);
   end Call_Store;

begin
   null;
end Main;
