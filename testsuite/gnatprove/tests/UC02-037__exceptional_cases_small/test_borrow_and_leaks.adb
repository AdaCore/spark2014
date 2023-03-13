procedure Test_Borrow_And_Leaks
  with
    SPARK_Mode => On
is

   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   E : exception;

   procedure Test_Borrow (L : access List_Cell) with
     Contract_Cases =>
       (L = null                         => L = null,
        L /= null and then L.Next = null =>
          L /= null and L.Next = null and L.Data = L.Data'Old,
        L /= null and then L.Next /= null and then L.Next.Next = null =>
          L /= null and L.Next /= null and L.Data = L.Data'Old and
          L.Next.Next = null and L.Next.Data = L.Next.Data'Old,
        others                           => False),
     Exceptional_Cases =>
       (E => L /= null and L.Next /= null and L.Next.Next /= null and
            L.Next.Next.Data = 0);

   procedure Test_Borrow (L : access List_Cell) is
      B1 : access List_Cell := L;
   begin
      if B1 /= null then
         declare
            B2 : access List_Cell := B1.Next;
         begin
            if B2 /= null then
               declare
                  B3 : access List_Cell := B2.Next;
               begin
                  if B3 /= null then
                     B3.Data := 0;
                     raise E;
                  end if;
               end;
            end if;
         end;
      end if;
   end Test_Borrow;

   procedure Test_Leak (L : access List_Cell) with
     Post => L.Next.Data = 0 and L.Next.Next.Next.Data = 0,
     Exceptional_Cases =>
       (E => Boolean'(L = null or else L.Next = null)'Old);

   procedure Test_Leak (L : access List_Cell) is
      X : constant List := new List_Cell'(0, null); --@RESOURCE_LEAK:FAIL
   begin
      if L = null then
         raise E;
      else
         X.Next := L.Next;
         L.Next := X;
         declare
            B : access List_Cell := L.Next.Next;
            Y : constant List := new List_Cell'(0, null); --@RESOURCE_LEAK:FAIL
         begin
            if B = null then
               raise E;
            else
               Y.Next := B.Next;
               B.Next := Y;
            end if;
         end;
      end if;
   end Test_Leak;

   procedure Raise_E with
     Post => False,
     Exceptional_Cases => (E => True);
   procedure Raise_E is
   begin
      raise E;
   end Raise_E;

   procedure Test_Borrow_Call (L : access List_Cell) with
     Contract_Cases =>
       (L = null                         => L = null,
        L /= null and then L.Next = null =>
          L /= null and L.Next = null and L.Data = L.Data'Old,
        L /= null and then L.Next /= null and then L.Next.Next = null =>
          L /= null and L.Next /= null and L.Data = L.Data'Old and
          L.Next.Next = null and L.Next.Data = L.Next.Data'Old,
        others                           => False),
     Exceptional_Cases =>
       (E => L /= null and L.Next /= null and L.Next.Next /= null and
            L.Next.Next.Data = 0);

   procedure Test_Borrow_Call (L : access List_Cell) is
      B1 : access List_Cell := L;
   begin
      if B1 /= null then
         declare
            B2 : access List_Cell := B1.Next;
         begin
            if B2 /= null then
               declare
                  B3 : access List_Cell := B2.Next;
               begin
                  if B3 /= null then
                     B3.Data := 0;
                     Raise_E;
                  end if;
               end;
            end if;
         end;
      end if;
   end Test_Borrow_Call;

   procedure Test_Leak_Call (L : access List_Cell) with
     Post => L.Next.Data = 0 and L.Next.Next.Next.Data = 0,
     Exceptional_Cases =>
       (E => Boolean'(L = null or else L.Next = null)'Old);

   procedure Test_Leak_Call (L : access List_Cell) is
      X : constant List := new List_Cell'(0, null); --@RESOURCE_LEAK:FAIL
   begin
      if L = null then
         raise E;
      else
         X.Next := L.Next;
         L.Next := X;
         declare
            B : access List_Cell := L.Next.Next;
            Y : constant List := new List_Cell'(0, null); --@RESOURCE_LEAK:FAIL
         begin
            if B = null then
               Raise_E;
            else
               Y.Next := B.Next;
               B.Next := Y;
            end if;
         end;
      end if;
   end Test_Leak_Call;

begin
   null;
end;
