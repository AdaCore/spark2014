pragma Ada_2012;
package body Good_Pack with SPARK_Mode => On is
    function Bad_Identity (arg : U64) return U64
	with Post => Bad_Identity'Result = arg - 1 is	-- purposefully fail to prove but without any gnat warning
    begin
	return arg;
    end Bad_Identity;

   ------------
   -- Square --
   ------------

   function Square (arg : U64) return U64 is
   begin
       return arg * Bad_Identity (arg);
   end Square;

end Good_Pack;
