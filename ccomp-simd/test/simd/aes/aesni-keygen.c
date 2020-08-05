// 128 bit key
static inline __m128i AES_128_ASSIST (__m128i temp1, __m128i temp2) {
  __m128i temp3;
  temp2 = _mm_shuffle_epi32 (temp2 ,0xff);
  temp3 = _mm_slli_si128 (temp1, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp3 = _mm_slli_si128 (temp3, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp3 = _mm_slli_si128 (temp3, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp1 = _mm_xor_si128 (temp1, temp2);
  return temp1;
}

void AES_128_Key_Expansion (const uint8_t *userkey, __m128i *key)
{
  __m128i temp1, temp2;
  temp1 = _mm_loadu_si128((__m128i*)userkey);
  key[0] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1 ,0x1);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[1] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x2);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[2] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x4);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[3] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x8);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[4] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x10);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[5] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x20);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[6] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x40);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[7] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x80);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[8] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x1b);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[9] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x36);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[10] = temp1;
}

// 192 bit key
static inline void KEY_192_ASSIST(__m128i* temp1, __m128i * temp2, __m128i * temp3) {
  __m128i temp4;
  *temp2 = _mm_shuffle_epi32 (*temp2, 0x55);
  temp4 = _mm_slli_si128 (*temp1, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  *temp1 = _mm_xor_si128 (*temp1, *temp2);
  *temp2 = _mm_shuffle_epi32(*temp1, 0xff);
  temp4 = _mm_slli_si128 (*temp3, 0x4);
  *temp3 = _mm_xor_si128 (*temp3, temp4);
  *temp3 = _mm_xor_si128 (*temp3, *temp2);
}

void AES_192_Key_Expansion (const uint8_t *userkey, __m128i *key)
{
  __m128i temp1, temp2, temp3;
  temp1 = _mm_loadu_si128((__m128i*)userkey);
  temp3 = _mm_loadu_si128((__m128i*)(userkey+16));
  key[0]=temp1;
  key[1]=temp3;
  temp2=_mm_aeskeygenassist_si128 (temp3,0x1);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[1] = (__m128i)_mm_shuffle_pd((__m128d)key[1], (__m128d)temp1, 0); 
  key[2] = (__m128i)_mm_shuffle_pd((__m128d)temp1, (__m128d)temp3, 1);
  temp2=_mm_aeskeygenassist_si128 (temp3,0x2);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[3]=temp1;
  key[4]=temp3;
  temp2=_mm_aeskeygenassist_si128 (temp3,0x4);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[4] = (__m128i)_mm_shuffle_pd((__m128d)key[4], (__m128d)temp1, 0);
  key[5] = (__m128i)_mm_shuffle_pd((__m128d)temp1, (__m128d)temp3, 1);
  temp2=_mm_aeskeygenassist_si128 (temp3,0x8);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[6]=temp1;
  key[7]=temp3;
  temp2=_mm_aeskeygenassist_si128 (temp3,0x10);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[7] = (__m128i)_mm_shuffle_pd((__m128d)key[7], (__m128d)temp1, 0);
  key[8] = (__m128i)_mm_shuffle_pd((__m128d)temp1, (__m128d)temp3, 1);
  temp2=_mm_aeskeygenassist_si128 (temp3,0x20);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[9]=temp1;
  key[10]=temp3;
  temp2=_mm_aeskeygenassist_si128 (temp3,0x40);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[10] = (__m128i)_mm_shuffle_pd((__m128d)key[10], (__m128d)temp1, 0);
  key[11] = (__m128i)_mm_shuffle_pd((__m128d)temp1, (__m128d)temp3, 1);
  temp2=_mm_aeskeygenassist_si128 (temp3,0x80);
  KEY_192_ASSIST(&temp1, &temp2, &temp3);
  key[12]=temp1;
}

// 256 bit key
static inline void KEY_256_ASSIST_1(__m128i* temp1, __m128i * temp2) {
  __m128i temp4;
  *temp2 = _mm_shuffle_epi32(*temp2, 0xff);
  temp4 = _mm_slli_si128 (*temp1, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp1 = _mm_xor_si128 (*temp1, temp4);
  *temp1 = _mm_xor_si128 (*temp1, *temp2);
}

static inline void KEY_256_ASSIST_2(__m128i* temp1, __m128i * temp3) {
  __m128i temp2,temp4;
  temp4 = _mm_aeskeygenassist_si128 (*temp1, 0x0);
  temp2 = _mm_shuffle_epi32(temp4, 0xaa);
  temp4 = _mm_slli_si128 (*temp3, 0x4);
  *temp3 = _mm_xor_si128 (*temp3, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp3 = _mm_xor_si128 (*temp3, temp4);
  temp4 = _mm_slli_si128 (temp4, 0x4);
  *temp3 = _mm_xor_si128 (*temp3, temp4);
  *temp3 = _mm_xor_si128 (*temp3, temp2);
}

void AES_256_Key_Expansion (const uint8_t *userkey, __m128i *key)
{
  __m128i temp1, temp2, temp3;
  temp1 = _mm_loadu_si128((__m128i*)userkey);
  temp3 = _mm_loadu_si128((__m128i*)(userkey+16));
  key[0] = temp1;
  key[1] = temp3;
  temp2 = _mm_aeskeygenassist_si128 (temp3, 0x01);
  KEY_256_ASSIST_1(&temp1, &temp2);
  key[2]=temp1;
  KEY_256_ASSIST_2(&temp1, &temp3);
  key[3]=temp3;
  temp2 = _mm_aeskeygenassist_si128  (temp3, 0x02);
  KEY_256_ASSIST_1(&temp1, &temp2);
  key[4]=temp1;
  KEY_256_ASSIST_2(&temp1, &temp3);
  key[5]=temp3;
  temp2 = _mm_aeskeygenassist_si128  (temp3, 0x04);
  KEY_256_ASSIST_1(&temp1, &temp2);
  key[6]=temp1;
  KEY_256_ASSIST_2(&temp1, &temp3);
  key[7]=temp3;
  temp2 = _mm_aeskeygenassist_si128 (temp3,0x08);
  KEY_256_ASSIST_1(&temp1, &temp2);
  key[8]=temp1;
  KEY_256_ASSIST_2(&temp1, &temp3);
  key[9]=temp3;
  temp2 = _mm_aeskeygenassist_si128 (temp3,0x10);
  KEY_256_ASSIST_1(&temp1, &temp2); 
  key[10]=temp1; 
  KEY_256_ASSIST_2(&temp1, &temp3); 
  key[11]=temp3;
  temp2 = _mm_aeskeygenassist_si128 (temp3,0x20);
  KEY_256_ASSIST_1(&temp1, &temp2); 
  key[12]=temp1; 
  KEY_256_ASSIST_2(&temp1, &temp3); 
  key[13]=temp3;
  temp2 = _mm_aeskeygenassist_si128 (temp3,0x40);
  KEY_256_ASSIST_1(&temp1, &temp2); 
  key[14]=temp1;
}

/* key-schedule for AES. Returns the number of rounds */
int AES_set_encrypt_key(const uint8_t *CIPHER_KEY, int key_length, __m128i *key){
  switch (key_length) {
  case 128:
    AES_128_Key_Expansion(CIPHER_KEY, key);
    break;
  case 192:
    AES_192_Key_Expansion(CIPHER_KEY, key); 
    break;
  case 256:
    AES_256_Key_Expansion(CIPHER_KEY, key);
    break;
  default:
    printf("wrong key size\n");
    exit(1);
  }
  return (key_length/32 + 6);
}

void AES_set_decrypt_key(int nr, __m128i *key, __m128i *decrypt_key){
  int i;
  decrypt_key[0] = key[nr];
  for (i=1; i<nr; i++) {
    decrypt_key[i] = _mm_aesimc_si128(key[nr-i]);
  }
  decrypt_key[nr] = key[0];
}


