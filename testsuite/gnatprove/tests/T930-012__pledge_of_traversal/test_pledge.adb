procedure Test_Pledge with SPARK_Mode is
   type Int_Access is not null access Integer;

   function Pledge (B : access constant Integer; P : Boolean) return Boolean is
     (P)
   with Ghost,
       Annotate => (GNATprove, Pledge);

   type R is record
      A, B : Int_Access;
   end record;

   function Get_1 (X : not null access R; C : Boolean) return not null access Integer with
     Post => Get_1'Result.all = (if C then X.A.all else X.B.all),
     Contract_Cases =>
       (C      => Pledge (Get_1'Result, X.A.all = Get_1'Result.all
                                        and X.B.all = X.B.all'Old),
        others => Pledge (Get_1'Result, X.B.all = Get_1'Result.all
                                        and X.A.all = X.A.all'Old));

   function Get_1 (X : not null access R; C : Boolean) return not null access Integer is
   begin
      if C then
         return X.A;
      else
         return X.B;
      end if;
   end Get_1;

   C_Glob : Boolean;

   function Get_2 (X : not null access R) return not null access Integer with
     Post => Get_2'Result.all = (if C_Glob then X.A.all else X.B.all),
     Contract_Cases =>
       (C_Glob => Pledge (Get_2'Result, X.A.all = Get_2'Result.all
                                        and X.B.all = X.B.all'Old),
        others => Pledge (Get_2'Result, X.B.all = Get_2'Result.all
                                        and X.A.all = X.A.all'Old));

   function Get_2 (X : not null access R) return not null access Integer is
   begin
      if C_Glob then
         return X.A;
      else
         return X.B;
      end if;
   end Get_2;

begin
   null;
end Test_Pledge;
