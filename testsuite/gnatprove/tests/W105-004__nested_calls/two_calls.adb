procedure Two_Calls
  with
    SPARK_Mode => On
is

   function Call_2 (F, G : not null access function return Integer; B : Boolean) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Always_Return),
     Depends => (Call_2'Result => (F, G, B)),
     Post => Call_2'Result = (if B then F.all else G.all);

   function Call_2 (F, G : not null access function return Integer; B : Boolean) return Integer is
   begin
      if B then
         return F.all;
      else
         return G.all;
      end if;
   end Call_2;

   function Cst_1 return Integer is (1);

   V : Integer := 0;
   function Read_V return Integer is (V);

   function Call_Call_First (F : not null access function return Integer; B : Boolean) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Call_Call_First'Result = Call_2 (F, Read_V'Access, B);

   function Call_Call_First (F : not null access function return Integer; B : Boolean) return Integer is
   begin
      if B then
         return F.all;
      else
         return Read_V;
      end if;
   end Call_Call_First;

   function Call_Call_Snd (F : not null access function return Integer; B : Boolean) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Call_Call_Snd'Result = Call_2 (Read_V'Access, F, B);

   function Call_Call_Snd (F : not null access function return Integer; B : Boolean) return Integer is
   begin
      if B then
         return Read_V;
      else
         return F.all;
      end if;
   end Call_Call_Snd;

   function Call_Call_Both (F : not null access function return Integer; B : Boolean) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Call_Call_Both'Result = Call_2 (F, F, B);

   function Call_Call_Both (F : not null access function return Integer; B : Boolean) return Integer is
   begin
      return F.all;
   end Call_Call_Both;

   function Rand (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   I : Integer;
begin
   I := Call_Call_First (Read_V'Access, Rand (1));
   pragma Assert (I = 0);
   I := Call_Call_Snd (Read_V'Access, Rand (2));
   pragma Assert (I = 0);
   I := Call_Call_Both (Read_V'Access, Rand (3));
   pragma Assert (I = 0);
end Two_Calls;
