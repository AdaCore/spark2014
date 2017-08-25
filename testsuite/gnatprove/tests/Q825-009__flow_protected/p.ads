package P is

   protected type PT is
      procedure Fetch (X : Integer; Y : out Integer)
      with Depends => (Y => (PT, X), PT =>+ null);

      procedure Proxy (X : Integer; Y : out Integer)
      with Depends => (Y => (PT, X), PT =>+ null);
   private
      Z : Integer := 0;
   end;

end;
