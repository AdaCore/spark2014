package body Red_Black_Trees with SPARK_Mode is

   procedure L_Balance (T : in out Tree) with
     Pre => not Is_Empty (T)
     and then Get (T).C = Black
     and then Is_Balanced (Child (T, Right))
     and then Nb_Blacks (Child (T, Left)) = Nb_Blacks (Child (T, Right))
     and then (if not Is_Empty (Child (T, Left))
                 then Is_Balanced (Child (Child (T, Left), Left))
               and then Is_Balanced (Child (Child (T, Left), Right))
               and then Nb_Blacks (Child (Child (T, Left), Left)) =
                 Nb_Blacks (Child (Child (T, Left), Right)))
     and then Is_Search_Tree (T),
     Post => Is_Balanced (T)
     and then Nb_Blacks (T) = Nb_Blacks (T'Old)
     and then Is_Search_Tree (T)
     and then Model (T'Old) <= Model (T)
     and then Model (T) <= Model (T'Old);

   procedure R_Balance (T : in out Tree) with
     Pre => not Is_Empty (T)
     and then Get (T).C = Black
     and then Is_Balanced (Child (T, Left))
     and then Nb_Blacks (Child (T, Left)) = Nb_Blacks (Child (T, Right))
     and then (if not Is_Empty (Child (T, Right))
                 then Is_Balanced (Child (Child (T, Right), Left))
               and then Is_Balanced (Child (Child (T, Right), Right))
               and then Nb_Blacks (Child (Child (T, Right), Left)) =
                 Nb_Blacks (Child (Child (T, Right), Right)))
     and then Is_Search_Tree (T),
     Post => Is_Balanced (T)
     and then Nb_Blacks (T) = Nb_Blacks (T'Old)
     and then Is_Search_Tree (T)
     and then Model (T'Old) <= Model (T)
     and then Model (T) <= Model (T'Old);

   procedure Insert_Internal (T : in out Tree; V : Integer) with
     Subprogram_Variant => (Decreases => Height (T)),
     Pre => Is_Balanced (T)
     and then Is_Search_Tree (T),
     Post => Is_Search_Tree (T)
     and then Contains (Model (T), V)
     and then Included_Except (Model (T), Model (T'Old), V)
     and then Model (T'Old) <= Model (T)
     and then Nb_Blacks (T) = Nb_Blacks (T'Old)
     and then (if Is_Empty (T'Old) or else Get (T'Old).C = Black
                 then Is_Balanced (T)
                   else Is_Balanced (Child (T, Left))
               and then Is_Balanced (Child (T, Right))
               and then Nb_Blacks (Child (T, Left)) = Nb_Blacks (Child (T, Right)));

   function Contains (T : Tree; V : Integer) return Boolean is
      C : Tree := T;
   begin
      while not Is_Empty (C) loop
         pragma Loop_Invariant (Is_Search_Tree (C));
         pragma Loop_Invariant
           (Contains (Model (T), V) = Contains (Model (C), V));
         pragma Loop_Variant (Decreases => Height (C));

         if Get (C).V = V then
            return True;
         elsif V < Get (C).V then
            C := Child (C, Left);
         else
            C := Child (C, Right);
         end if;
      end loop;
      return False;
   end Contains;

   procedure L_Balance (T : in out Tree) is
      T_Old : constant Tree := T with Ghost;
      L : constant Tree := Child (T, Left);
      R : constant Tree := Child (T, Right);
   begin
      if not Is_Empty (L) and then Get (L).C = Red then
         declare
            LL : constant Tree := Child (L, Left);
            LR : constant Tree := Child (L, Right);
         begin
            if not Is_Empty (LL) and then Get (LL).C = Red then
               declare
                  New_L : constant Tree := Set_Root (LL, (Get (LL).V, Black));
                  New_R : constant Tree := Set_Child (T, Left, LR);
               begin
                  T := Create (Get (L), (New_L, New_R));
               end;
            elsif not Is_Empty (LR) and then Get (LR).C = Red then
               declare
                  LRL   : constant Tree := Child (LR, Left);
                  LRR   : constant Tree := Child (LR, Right);
                  New_L : constant Tree := Create ((Get (L).V, Black), (LL, LRL));
                  New_R : constant Tree := Set_Child (T, Left, LRR);
               begin
                  T := Create (Get (LR), (New_L, New_R));
               end;
            end if;
         end;
      end if;
   end L_Balance;

   procedure R_Balance (T : in out Tree) is
      T_Old : constant Tree := T with Ghost;
      L : constant Tree := Child (T, Left);
      R : constant Tree := Child (T, Right);
   begin
      if not Is_Empty (R) and then Get (R).C = Red then
         declare
            RL : constant Tree := Child (R, Left);
            RR : constant Tree := Child (R, Right);
         begin
            if not Is_Empty (RR) and then Get (RR).C = Red then
               declare
                  New_L : constant Tree := Set_Child (T, Right, RL);
                  New_R : constant Tree := Set_Root (RR, (Get (RR).V, Black));
               begin
                  T := Create (Get (R), (New_L, New_R));
               end;
            elsif not Is_Empty (RL) and then Get (RL).C = Red then
               declare
                  RLL   : constant Tree := Child (RL, Left);
                  RLR   : constant Tree := Child (RL, Right);
                  New_L : constant Tree := Set_Child (T, Right, RLL);
                  New_R : constant Tree := Create ((Get (R).V, Black), (RLR, RR));
               begin
                  T := Create (Get (RL), (New_L, New_R));
               end;
            end if;
         end;
      end if;
   end R_Balance;

   procedure Insert_Internal (T : in out Tree; V : Integer) is
   begin
      if Is_Empty (T) then
         T := Create ((V, Red));
      elsif V = Get (T).V then
         null;
      elsif Get (T).V < V then
         declare
            C : Tree := Child (T, Right);
         begin
            Insert_Internal (C, V);
            T := Set_Child (T, Right, C);
         end;
         if Get (T).C = Black then
            R_Balance (T);
         end if;
      else
         declare
            C : Tree := Child (T, Left);
         begin
            Insert_Internal (C, V);
            T := Set_Child (T, Left, C);
         end;
         if Get (T).C = Black then
            L_Balance (T);
         end if;
      end if;
   end Insert_Internal;

   procedure Insert (T : in out Tree; V : Integer) is
   begin
      Insert_Internal (T, V);
      if Get (T).C = Red then
         T := Set_Root (T, (Get (T).V, Black));
      end if;
   end Insert;

end Red_Black_Trees;
