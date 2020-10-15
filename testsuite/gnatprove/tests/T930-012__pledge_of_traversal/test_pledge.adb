procedure Test_Pledge with SPARK_Mode is
   type Int_Access is not null access Integer;

   function At_End_Borrow (I : access constant Integer) return access constant Integer is
     (I)
   with Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   type R is record
      A, B : Int_Access;
   end record;

   function At_End_Borrow (X : access constant R) return access constant R is
     (X)
   with Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function Get_1 (X : not null access R; C : Boolean) return not null access Integer with
     Post => Get_1'Result.all = (if C then X.A.all else X.B.all),
     Contract_Cases =>
       (C      => At_End_Borrow (X).A.all = At_End_Borrow (Get_1'Result).all
          and At_End_Borrow (X).B.all = X.B.all,
        others => At_End_Borrow (X).B.all = At_End_Borrow (Get_1'Result).all
          and At_End_Borrow (X).A.all = X.A.all);

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
       (C_Glob => At_End_Borrow (X).A.all = At_End_Borrow (Get_2'Result).all
          and At_End_Borrow (X).B.all = X.B.all,
        others => At_End_Borrow (X).B.all = At_End_Borrow (Get_2'Result).all
          and At_End_Borrow (X).A.all = X.A.all);

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
