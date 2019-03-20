package P is
   protected type PT is
      function S1 (X : Float) return Float;
      function S2 (X : Float) return Float;
      function S3 (X : Float) return Float;
      --  Those are just protected wrappers around predefined trigonometric
      --  functions coming from instances of
      --  Ada.Numerics.Generic_Elementary_Functions; they are non-blocking.

      procedure Print (X : Float);
      --  This is a wrapper around a Text_IO routine in an instance of a
      --  predefined generic; this routine is potentially blocking.

   end PT;
end;
