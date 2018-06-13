Мне иногда бывает нужно сгенерировать картинку по формуле.
```
im 300x300 (1, 0, 0) result.png
```
![result.png](../assets/1.png)

```
im 300x300 (t = 1 - (2*nxy - vec2(1)).sqlen; t, t, 0) result.png
```
![result.png](../assets/2.png)

```
im 300x300x30 (hsv2rgb(nf, 1, 1 - (2*nxy - vec2(1)).sqlen)) r%f%.png
```
![results](../assets/3.png)