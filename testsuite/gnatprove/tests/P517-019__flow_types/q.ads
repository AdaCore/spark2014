package Q is
   X : Integer := 0;

   type T1 (D : Integer := X) is limited private;
   type T2 (D : Integer := X) is limited private;
   type T3 (D : Integer := X) is limited private;
   type T4 (D : Integer := X);
   type T5 (D : Integer := X);

   task type      T4 (D : Integer := X);
   protected type T5 (D : Integer := X) is end;
private
   task type T1      (D : Integer := X);
   protected type T2 (D : Integer := X) is end;
   type T3           (D : Integer := X) is record null; end record;
end Q;
