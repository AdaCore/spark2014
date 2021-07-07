with Ext;
procedure Bad_Access with SPARK_Mode is
   procedure Do_Nothing (X : aliased in out Ext.R) is
      Y : access Ext.R := X'Access;
   begin
      null;
   end Do_Nothing;

   function Rand (I : Integer) return Boolean with Import;
   type Int_Acc is access Integer;

   procedure Do_Something is
   begin
      if Rand (0) then
         declare
            X : Int_Acc := new Integer'(3);
         begin
            return;
         end;
      elsif Rand (1) then
         declare
            package Nested is
               X : Int_Acc := new Integer'(3);
            end Nested;
         begin
            return;
         end;
      elsif Rand (2) then
         declare
            package Nested is
               type T is private;
            private
               type T is new Integer;
               X : Int_Acc := new Integer'(3);
            end Nested;
         begin
            return;
         end;
      elsif Rand (3) then
         declare
            package Nested is
               procedure P;
            end Nested;
            package body Nested is
               X : Int_Acc := new Integer'(3);
               procedure P is null;
            end Nested;
         begin
            return;
         end;
      elsif Rand (4) then
         declare
            package Nested is
               procedure P;
            end Nested;
            package body Nested is
               procedure P is null;
            begin
               declare
                  X : Int_Acc := new Integer'(3);
               begin
                  goto End_Of_Scope;
               end;
               <<End_Of_Scope>>
            end Nested;
         begin
            null;
         end;
      elsif Rand (5) then
         declare
            package Nested is
               procedure P;
            end Nested;
            package body Nested is
               procedure P is null;
            begin
               declare
                  X : Integer := 3;
               begin
                  goto End_Of_Scope;
               end;
               <<End_Of_Scope>>
            end Nested;
         begin
            null;
         end;
      end if;
   end Do_Something;

   function Id (X : Integer) return Integer with Import,
     SPARK_Mode => Off;

   type Id_Acc is access function (X : Integer) return Integer;

   X : Id_Acc := Id'Access;
begin
   null;
end Bad_Access;
