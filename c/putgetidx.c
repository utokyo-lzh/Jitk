int v[4];

int
put(unsigned int idx, int x)
{
  if (idx < 4) {
    v[idx] = x;
    return 0;
  } else {
    return -1;
  }
}

int
get(unsigned int idx)
{
  if (idx < 4) {
    return v[idx];
  } else {
    return -1;
  }
}
