procedure Wrong_Warning with SPARK_Mode is
   type Int_Acc is not null access Integer;
   type Map;
   type Map_Acc is access Map;
   type Map is record
      Key   : Positive;
      Value : Int_Acc;
      Next  : Map_Acc;
   end record;

   procedure Replace_Element (M : access Map; K : Positive; V : Integer) is
      X : access Map := M;
   begin
      while X /= null loop
         if X.Key = K then
            X.Value.all := V;
            return;
         end if;
         X := X.Next;
      end loop;
   end Replace_Element;
begin
   null;
end Wrong_Warning;
