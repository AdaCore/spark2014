package Import_Intrinsic is
   type New_Float is private;
   function "<" (Left, Right : New_Float) return Boolean;
   function Create (F : Float) return New_Float;
private
   type New_Float is new Float;
   pragma Import (Intrinsic, "<");
   function Create (F : Float) return New_Float is (New_Float (F));
end Import_Intrinsic;
