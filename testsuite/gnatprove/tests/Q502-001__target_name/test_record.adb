procedure Test_Record with SPARK_Mode is
   type With_Discr (D : Boolean) is record
      case D is
      when True  => F : Integer;
      when False => null;
      end case;
   end record;

   type Mut_Discr (D : Boolean := False) is record
      case D is
      when True  => F : Integer;
      when False => null;
      end case;
   end record;

   type With_Tag is tagged record
      F : Integer;
   end record;

   type Child is new With_Tag with record
      G : Integer;
   end record;

   procedure P1 (X : in out With_Discr) with
     Pre => X.D = True and then X.F < 10
   is
   begin
      X := (True, @.F + 1);
      X.F := @ + 1;
   end P1;

   procedure P2 (X : in out Mut_Discr) with
     Pre => not X'Constrained and (if X.D then X.F < 10)
   is
   begin
      X := (True, (if @.D then @.F + 1 else 0));
      X.F := @ + 1;
   end P2;

   procedure P3 (X : in out Child) with
     Pre => X.F < 10 and X.G < 10
   is
   begin
      X := (@.F + 1, @.G + 1);
      X.F := @ + 1;
      With_Tag (X) := (F => @.F + 1);
   end P3;
begin
   null;
end Test_Record;
