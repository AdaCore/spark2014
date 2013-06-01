
     --=================================================================--

package body FB20A00 is

   function Find ( Str : in String ;
                   Sub : in String ) return Boolean is

      New_Str : String (Str'First .. Str'Last);
      New_Sub : String (Sub'First .. Sub'Last);

      Pos : Integer := Str'First ;             -- Character index.


      function Upper_Case (Str : in String) return String is
         subtype Upper is Character range 'A' .. 'Z' ;
         subtype Lower is Character range 'a' .. 'z' ;
         Ret : String (Str'First .. Str'Last) ;
         Pos : Integer;
      begin
         for I in Str'Range loop
            if ( Str (I) in Lower ) then
               Pos := Upper'Pos (Upper'First) +
                      ( Lower'Pos (Str(I)) - Lower'Pos(Lower'First) ) ;
               Ret (I) := Upper'Val (Pos) ;
            else
               Ret (I) := Str (I);
            end if ;
         end loop ;
         return (Ret) ;
      end Upper_Case;

   begin
      New_Str := Upper_Case (Str);             -- Convert Str and Sub to upper
      New_Sub := Upper_Case (Sub);             -- case for comparison.

      while ( Pos <= New_Str'Last-New_Sub'Length+1 )  -- Search until no more
        and then                                      -- sub-string-length
        ( New_Str ( Pos .. Pos+New_Sub'Length-1 ) /= New_Sub ) -- slices
                                                               -- remain.
      loop
         Pos := Pos + 1 ;
      end loop ;

      if ( Pos > New_Str'Last-New_Sub'Length+1 ) then  -- Substring not found.
         return (False);
      else
         return (True);
      end if ;

   end Find;

end FB20A00;
