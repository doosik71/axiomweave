# AxiomWeave 커널 명세 (Kernel Specification)

> **문서 상태:** 초안(Draft) · 단편 L0 · 대상 버전 v0.1  
> 상위 문서: [specification.md](specification.md), 논리 규칙: [logic-spec.md](logic-spec.md), 생성 측: [language-spec.md](language-spec.md). 이 문서는 AxiomCore 커널의 입력 형식(증명 객체와 인증서), 정규화와 해시, 이름 구문, 허용 공리 정책, 검증 알고리즘, 결과와 오류, 신뢰 기반을 정의한다. 규범적 표현은 [specification.md §1.1](specification.md#11-규범적-표현)을 따른다.

## 1. 범위

logic-spec은 커널이 **무엇을** 인정하는지 정의하고, 이 문서는 커널이 그것을 **어떻게** 입력받아 검사하는지 정의한다. 두 문서가 충돌하면 logic-spec의 규칙이 우선하며, 이 문서는 logic-spec을 따르도록 개정해야 한다.

| 포함                                                    | 제외                                          |
| ------------------------------------------------------- | --------------------------------------------- |
| 이름 구문 (원자, 가정, 선언)                            | 추론 규칙의 정의 (logic-spec)                 |
| 명제와 도출 트리의 JSON 인코딩                          | Python DSL과 Elaboration (language-spec)      |
| 인증서(`.axwp`) 번들 형식, 정규화, SHA-256 해시         | L1 이후의 항, 바인더, 이름 표현               |
| 허용 공리 목록의 형식과 전달                            | 증명 탐색, 전술, 외부 백엔드                  |
| 검증 알고리즘, 결과 상태, 오류 코드, 자원 제한          |                                               |
| 커널의 신뢰 기반과 모듈 경계                            |                                               |

## 2. 설계 결정 요약

[specification.md §9](specification.md#9-미결-사항)에서 이 문서에 위임한 항목은 다음과 같이 확정한다.

| 항목                     | 결정                                                                                         |
| ------------------------ | -------------------------------------------------------------------------------------------- |
| 이름 표현                | L0는 바인더가 없으므로 원자와 가정을 이름으로 직접 표현한다. de Bruijn 등은 L1에서 결정한다. |
| 증명 객체 인코딩         | 규칙 태그가 붙은 도출 트리. 노드 하나가 logic-spec 규칙 적용 하나에 대응한다.                 |
| 인증서 단위              | 자기완결 번들. Theory 하나의 검증에 필요한 모든 공리·정리·증명을 한 파일에 담는다.            |
| 직렬화                   | UTF-8 JSON. 해시는 정규 JSON 바이트에 대한 SHA-256이다.                                       |
| 허용 공리 목록           | 이름과 선언 해시의 쌍. 검증자가 인증서 바깥에서 지정하며, 인증서 내용을 따르지 않는다.        |
| 커널 입력 경계           | 커널의 진입점은 JSON 바이트만 받는다. 같은 프로세스에서 호출하더라도 DSL 객체를 받지 않는다.  |

## 3. 이름 구문

### 3.1. 식별자

```text
identifier ::= [A-Za-z_][A-Za-z0-9_]*
```

- 식별자는 ASCII 문자로만 구성되며 길이는 1 이상 255 이하여야 한다.
- 예약어 `and`, `or`, `imp`, `false`는 원자 이름과 가정 이름으로 사용할 수 없다.

### 3.2. 이름의 종류

| 종류         | 구문                                      | 예                          | 이름 공간           |
| ------------ | ----------------------------------------- | --------------------------- | ------------------- |
| 명제 원자    | 예약어가 아닌 `identifier`                | `P`, `Q1`, `goal_x`         | 원자                |
| 가정 이름    | 예약어가 아닌 `identifier`                | `h1`, `hp`                  | 증명 하나 안의 가정 |
| 선언 이름    | `identifier ("." identifier)+`            | `classical.em`, `demo.logic.and_comm` | 번들 전체 |

- 선언 이름은 점으로 구분된 두 개 이상의 식별자이며, 전체 길이는 1023 이하여야 한다. 마지막 식별자를 제외한 부분이 Theory 이름이다 ([language-spec.md §5.1](language-spec.md#51-생성)).
- 선언 이름의 식별자에는 예약어 제한이 없다.
- 원자와 가정은 서로 다른 이름 공간에 속하므로 같은 문자열을 써도 충돌하지 않는다 ([logic-spec.md §5.1](logic-spec.md#51-문맥)).
- 이 규칙은 [language-spec.md §4.2](language-spec.md#42-원자와-상수)의 잠정 규칙을 확정한다.

## 4. 명제 인코딩

L0 명제는 첫 원소가 태그인 JSON 배열로 인코딩한다.

| 명제                   | JSON                         |
| ---------------------- | ---------------------------- |
| 원자 $p$               | `["atom", "p"]`              |
| $\bot$                 | `["false"]`                  |
| $A \land B$            | `["and", A, B]`              |
| $A \lor B$             | `["or", A, B]`               |
| $A \to B$              | `["imp", A, B]`              |

- 배열 `["and", A, B]`는 logic-spec의 항 $\mathsf{and}\ A\ B$, 즉 $(\mathsf{and}\ A)\ B$에 대응한다. 부분 적용 항은 이 인코딩으로 표현할 수 없으므로, 디코딩에 성공한 값은 모두 타입 $\mathsf{Prop}$을 갖는다 ([logic-spec.md §3.4](logic-spec.md#34-항)).
- 태그가 위 다섯 개가 아니거나, 원소 수가 맞지 않거나, 원자 이름이 [3.2](#32-이름의-종류)의 구문을 따르지 않으면 커널은 거부해야 한다.
- `lam`, `forall`, `exists`, `eq` 등 L0 밖의 태그는 단편 위반(`E_FRAGMENT`)으로, 그 밖의 알 수 없는 태그는 형식 오류(`E_FORMAT`)로 보고해야 한다.
- 축약 표기($\lnot$, $\top$, $\leftrightarrow$)에 해당하는 태그는 존재하지 않는다 ([logic-spec.md §4](logic-spec.md#4-축약-표기)).

명제의 동등성은 디코딩된 트리의 구조적 동일성이다 ([logic-spec.md §3.6](logic-spec.md#36-항의-동등성)).

## 5. 도출 트리 인코딩

도출은 JSON 객체의 트리이다. 모든 노드는 `rule` 키를 가지며, 규칙마다 정해진 키 집합을 **정확히** 가져야 한다. 키가 빠지거나 남는 노드는 거부해야 한다.

| `rule`    | 규칙                 | 나머지 키와 값                                                                                      |
| --------- | -------------------- | --------------------------------------------------------------------------------------------------- |
| `hyp`     | $\mathrm{Hyp}$       | `name`: 가정 이름                                                                                   |
| `and_i`   | $\land\mathrm{I}$    | `left`: $A$의 도출, `right`: $B$의 도출                                                             |
| `and_e1`  | $\land\mathrm{E}_1$  | `of`: $A \land B$의 도출                                                                            |
| `and_e2`  | $\land\mathrm{E}_2$  | `of`: $A \land B$의 도출                                                                            |
| `or_i1`   | $\lor\mathrm{I}_1$   | `of`: $A$의 도출, `right`: 명제 $B$                                                                 |
| `or_i2`   | $\lor\mathrm{I}_2$   | `left`: 명제 $A$, `of`: $B$의 도출                                                                  |
| `or_e`    | $\lor\mathrm{E}$     | `of`: $A \lor B$의 도출, `left_name`, `left`: $h_1 : A$ 아래 $C$의 도출, `right_name`, `right`: $h_2 : B$ 아래 $C$의 도출 |
| `imp_i`   | $\to\mathrm{I}$      | `name`: 가정 이름, `hyp`: 가정 명제 $A$, `body`: $h : A$ 아래 $B$의 도출                            |
| `imp_e`   | $\to\mathrm{E}$      | `fn`: $A \to B$의 도출, `arg`: $A$의 도출                                                           |
| `false_e` | $\bot\mathrm{E}$     | `of`: $\bot$의 도출, `goal`: 결론 명제 $A$                                                          |
| `thm`     | $\mathrm{Thm}$       | `name`: 정리의 선언 이름, `hash`: 그 선언의 해시, `subst`: 치환                                     |
| `ax`      | $\mathrm{Ax}$        | `name`: 공리의 선언 이름, `hash`: 그 선언의 해시, `subst`: 치환                                     |

- 각 노드가 담는 정보는 [logic-spec.md §8.5](logic-spec.md#85-결론-재계산에-필요한-정보-참고)의 표와 같다. 도출 노드는 결론 명제를 기록하지 않는다. 커널은 결론을 항상 재계산한다.
- 치환 `subst`는 원자 이름을 키로, 명제를 값으로 하는 JSON 객체이다. 빈 치환은 `{}`이다.
- `thm`/`ax` 노드의 `hash`는 참조하는 선언의 해시([7.3](#73-선언-해시))이며, 커널이 다시 계산한 값과 같아야 한다.

## 6. 인증서 번들

### 6.1. 구조

인증서는 다음 키를 정확히 가진 JSON 객체이다.

| 키               | 값                                                                                   |
| ---------------- | ------------------------------------------------------------------------------------ |
| `format`         | 문자열 `"axwp"`                                                                      |
| `format_version` | 정수 `1`                                                                             |
| `spec_version`   | 생성 시 따른 명세 버전 문자열 (v0.1은 `"0.1"`)                                       |
| `fragment`       | 논리 단편 식별자 (v0.1은 `"L0"`)                                                     |
| `kernel_version` | 생성 측 커널의 버전 문자열 (정보용)                                                  |
| `theory`         | 내보낸 Theory의 이름                                                                 |
| `declarations`   | 선언 객체의 배열. 배열 순서가 환경의 순서이다.                                        |
| `bundle_hash`    | 번들 해시 ([7.4](#74-번들-해시))                                                     |

선언 객체는 다음 키를 정확히 가진다.

| 키          | 공리 (`axiom`)      | 정리 (`theorem`)                                             |
| ----------- | ------------------- | ------------------------------------------------------------ |
| `kind`      | `"axiom"`           | `"theorem"`                                                  |
| `name`      | 선언 이름           | 선언 이름                                                    |
| `statement` | 명제                | 명제                                                         |
| `proof`     | 없음                | 도출 트리                                                    |
| `hash`      | 선언 해시           | 선언 해시                                                    |
| `axioms`    | 없음                | 의존 공리 선언 이름의 배열 (코드 포인트 오름차순, 중복 없음) |

### 6.2. 자기완결성

- 번들은 `theory`의 검증에 필요한 모든 선언을 포함해야 한다. 즉 가져온 Theory의 공리와 정리, 그 정리들의 증명, 그리고 `theory` 자신의 공리와 `VERIFIED` 정리를 [language-spec.md §5.1](language-spec.md#51-생성)의 선언 순서대로 포함한다.
- 커널은 번들 밖의 파일, 저장소, 네트워크를 참조해서는 안 된다. 번들 하나만으로 모든 선언을 처음부터 검증한다.
- `thy.export`가 기록하는 번들에는 `VERIFIED` 정리만 넣는다 ([language-spec.md §8](language-spec.md#8-인증서와-명령행)). `Theory.check()`가 검증을 위해 만드는 번들에는 Elaboration에 성공한 정리를 넣으며, 그 결과는 커널이 정한다 ([language-spec.md §5.6](language-spec.md#56-검증)).

### 6.3. 버전 필드

- 커널은 `format`이 `"axwp"`가 아니거나 지원하지 않는 `format_version`, `fragment`를 가진 번들을 `E_VERSION`으로 거부해야 한다. v0.1 커널이 지원하는 값은 `format_version = 1`, `fragment = "L0"`뿐이다.
- `spec_version`과 `kernel_version`은 재현을 위한 기록이며, 검증 결과에 영향을 주어서는 안 된다. 같은 번들의 검증 결과는 **검증하는** 커널의 버전에만 의존한다.

## 7. 정규화와 해시

### 7.1. 허용되는 JSON

커널이 받는 JSON은 다음 제한을 만족해야 하며, 위반 시 `E_FORMAT`으로 거부해야 한다.

- 인코딩은 UTF-8이며 BOM이 없어야 한다.
- 값은 객체, 배열, 문자열, 정수만 허용한다. `null`, `true`/`false`, 실수, `NaN`/`Infinity`는 허용하지 않는다.
- 정수는 `format_version`에만 나타나며 0 이상이어야 한다.
- 모든 문자열은 출력 가능한 ASCII(0x20–0x7E)로만 구성되어야 한다. L0에서 문자열은 태그, 이름, 버전, 해시뿐이다.
- 한 객체 안에 같은 키가 두 번 나타나서는 안 된다.

인증서 파일 자체는 정규형일 필요가 없다 (들여쓰기, 키 순서 자유). 해시는 아래의 정규형으로 계산한다.

### 7.2. 정규 JSON

값 $v$의 정규 바이트 $\mathrm{canon}(v)$는 다음 규칙으로 만든 ASCII 바이트열이다.

1. 객체의 키는 코드 포인트 오름차순으로 정렬한다.
2. 구분자는 `,`와 `:`이며, 의미 없는 공백을 넣지 않는다.
3. 문자열은 `"`와 `\`만 `\"`, `\\`로 이스케이프하고, 그 밖의 문자는 그대로 쓴다 ([7.1](#71-허용되는-json)에 따라 제어 문자는 존재하지 않는다).
4. 정수는 앞자리 0 없는 10진수로 쓴다.

Python에서는 `json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=True)`를 ASCII로 인코딩한 결과가 위 규칙과 일치한다. 단, Python의 `bool`이 `int`의 하위 클래스이므로 `True`/`False`가 정수로 섞여 들어가지 않도록 먼저 [7.1](#71-허용되는-json)을 검사해야 한다.

### 7.3. 선언 해시

선언의 해시는 다음과 같다.

$$
\mathrm{hash}(d) = \texttt{"sha256:"} \mathbin{+\!\!+} \mathrm{hex}(\mathrm{SHA256}(\mathrm{canon}(d^{\circ})))
$$

여기서 $d^{\circ}$는 선언 객체에서 `hash`와 `axioms` 키를 뺀 객체(`kind`, `name`, `statement`, 그리고 정리의 경우 `proof`)이고, $\mathrm{hex}$는 소문자 16진수 64자이다.

- 선언 해시는 선언 이름, 명제, 증명을 함께 식별한다. [specification.md §7](specification.md#7-인증서와-재현성)의 "명제와 증명 객체의 내용 해시"는 이 해시로 충족한다.
- `axioms`는 커널이 계산하는 파생 정보이므로 해시에 포함하지 않는다. 대신 커널은 기록된 `axioms`가 계산값과 같은지 검사한다 ([8.3](#83-선언-검사)).

### 7.4. 번들 해시

`bundle_hash`는 번들 객체에서 `bundle_hash` 키를 뺀 객체 $b^{\circ}$에 대해 $\texttt{"sha256:"} \mathbin{+\!\!+} \mathrm{hex}(\mathrm{SHA256}(\mathrm{canon}(b^{\circ})))$이다. 커널은 이 값을 다시 계산하여 기록과 다르면 `E_HASH_MISMATCH`로 번들 전체를 거부해야 한다. 번들 해시는 인증서 파일을 식별하고 전송 중 변조를 드러내기 위한 것이며, 검증의 근거는 아니다.

## 8. 검증 알고리즘

### 8.1. 진입점

커널의 공개 진입점은 다음 하나이다.

```python
check_bundle(data: bytes, allowed_axioms: Mapping[str, str]) -> KernelReport
```

- `data`는 인증서 파일의 바이트이다. 커널은 Python DSL 객체(`Prop`, `Theorem` 등)를 받아서는 안 된다. `Theory.check()`가 같은 프로세스에서 커널을 호출할 때도 번들을 직렬화한 바이트를 전달해야 한다 ([language-spec.md §5.6](language-spec.md#56-검증)).
- `allowed_axioms`는 허용 공리 정책이다 ([9](#9-허용-공리-정책)).
- 커널은 예외 없이 `KernelReport`를 반환해야 한다. 내부 오류를 포함한 모든 실패는 거부로 보고한다.

### 8.2. 단계

| 단계 | 내용                                                                                             | 실패 시                    |
| ---- | ------------------------------------------------------------------------------------------------ | -------------------------- |
| 1    | 크기 제한 검사 후 JSON 파싱, [7.1](#71-허용되는-json) 제한 검사                                   | 번들 전체 거부             |
| 2    | 번들 구조, 버전 필드, `bundle_hash` 검사                                                         | 번들 전체 거부             |
| 3    | 모든 선언 객체의 구조, 이름 구문, 명제·도출 인코딩, 깊이 제한 검사                               | 번들 전체 거부             |
| 4    | 선언 이름의 중복 검사                                                                            | 번들 전체 거부             |
| 5    | 공리 선언이 모두 허용 정책을 만족하는지 검사 ([logic-spec.md §8.3](logic-spec.md#83-공리-허용-정책)) | 번들 전체 거부 (환경 거부) |
| 6    | 선언을 배열 순서대로 [8.3](#83-선언-검사)에 따라 검사                                            | 해당 선언만 거부           |

1–5단계에서 실패하면 어떤 선언도 `VERIFIED`가 되지 않는다.

### 8.3. 선언 검사

커널은 수락된 선언의 목록 $E$를 유지한다. 처음에 $E$는 비어 있다. 각 선언 $d$에 대해:

1. $\mathrm{hash}(d)$를 계산하여 기록된 `hash`와 비교한다. 다르면 거부한다 (`E_HASH_MISMATCH`).
2. 공리이면 $E$에 추가하고 수락한다.
3. 정리이면 `proof`를 빈 문맥에서 [8.4](#84-결론-재계산)로 재계산하여 결론 $C$와 의존 공리 집합 $X$를 얻는다. 재계산 중 오류가 있으면 거부한다.
4. $C$가 `statement`와 구조적으로 같지 않으면 거부한다 (`E_CONCLUSION_MISMATCH`).
5. $X$를 정렬한 배열이 기록된 `axioms`와 같지 않으면 거부한다 (`E_AXIOMS_MISMATCH`).
6. 모두 통과하면 $d$를 $E$에 추가하고 `VERIFIED`로 보고한다.

거부된 정리는 $E$에 추가하지 않는다. 따라서 그 정리를 참조하는 뒤의 증명은 `E_UNKNOWN_DECL`로 거부된다. 이는 [logic-spec.md §7.2](logic-spec.md#72-환경-적격성)의 환경 적격성과 일치하며, 자기 자신이나 뒤에 오는 선언에 대한 참조(순환 참조)도 같은 방식으로 거부된다.

### 8.4. 결론 재계산

$\mathrm{infer}(E, \Gamma, D)$는 도출 노드 $D$의 결론과 의존 공리 집합을 계산하거나 오류를 낸다. $\Gamma$는 가정 이름에서 명제로 가는 유한 사상이다. 각 규칙은 logic-spec §8.1을 그대로 구현한다.

| `rule`    | 계산                                                                                                                         | 오류                                       |
| --------- | ---------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| `hyp`     | $\Gamma(h)$                                                                                                                  | $h \notin \mathrm{dom}(\Gamma)$: `E_HYP_UNKNOWN` |
| `and_i`   | `left`의 결론 $A$, `right`의 결론 $B$ → $A \land B$                                                                           | —                                          |
| `and_e1`  | `of`의 결론이 $A \land B$ → $A$                                                                                              | 형태 불일치: `E_RULE_MISMATCH`             |
| `and_e2`  | `of`의 결론이 $A \land B$ → $B$                                                                                              | 형태 불일치: `E_RULE_MISMATCH`             |
| `or_i1`   | `of`의 결론 $A$ → $A \lor B$ (`right` $= B$)                                                                                 | —                                          |
| `or_i2`   | `of`의 결론 $B$ → $A \lor B$ (`left` $= A$)                                                                                  | —                                          |
| `or_e`    | `of`의 결론이 $A \lor B$; $\Gamma, h_1 : A$에서 `left`의 결론 $C_1$; $\Gamma, h_2 : B$에서 `right`의 결론 $C_2$; $C_1 \equiv C_2$ → $C_1$ | 형태 불일치·$C_1 \not\equiv C_2$: `E_RULE_MISMATCH`; $h_i \in \mathrm{dom}(\Gamma)$: `E_HYP_NOT_FRESH` |
| `imp_i`   | $\Gamma, h : A$에서 `body`의 결론 $B$ → $A \to B$                                                                             | $h \in \mathrm{dom}(\Gamma)$: `E_HYP_NOT_FRESH` |
| `imp_e`   | `fn`의 결론이 $A \to B$, `arg`의 결론 $A' \equiv A$ → $B$                                                                     | 형태 불일치·$A' \not\equiv A$: `E_RULE_MISMATCH` |
| `false_e` | `of`의 결론이 $\bot$ → `goal`                                                                                                | 형태 불일치: `E_RULE_MISMATCH`             |
| `thm`     | $E$에서 이름이 `name`인 정리 $d$를 찾고 `hash` $= \mathrm{hash}(d)$, $\mathrm{dom}(\sigma) \subseteq \mathrm{atoms}(d.\mathit{statement})$ 확인 → $d.\mathit{statement}[\sigma]$ | 없음·종류 불일치: `E_UNKNOWN_DECL`; 해시 불일치: `E_HASH_MISMATCH`; 정의역 위반: `E_SUBST_DOMAIN` |
| `ax`      | `thm`과 같되 공리를 찾는다                                                                                                   | `thm`과 같음                               |

의존 공리 집합은 [logic-spec.md §8.4](logic-spec.md#84-공리-의존성)에 따라 계산한다. `ax`는 $\lbrace \mathit{name} \rbrace$, `thm`은 참조한 정리의 $X$, 나머지는 전제들의 합집합이다.

- 치환은 동시 치환이다 ([logic-spec.md §6.1](logic-spec.md#61-치환)).
- `or_e`의 두 분기에서 $h_1 = h_2$는 허용된다. 두 분기는 서로 독립인 문맥에서 계산한다.
- 오류가 나면 해당 선언에 대해 처음 발견한 오류 하나를 보고한다. 하위 노드는 키 순서가 아니라 위 표의 키 나열 순서(예: `or_e`는 `of`, `left`, `right`)로 방문해야 하며, 이로써 같은 입력에 대해 같은 오류가 보고된다.

### 8.5. 자원 제한

악의적이거나 손상된 인증서가 검증기를 중단시키지 못하도록 커널은 다음 제한을 적용해야 한다. 제한 값은 커널 설정으로 바꿀 수 있으나, 기본값은 아래와 같다.

| 항목                                   | 기본값          |
| -------------------------------------- | --------------- |
| 인증서 파일 크기                       | 64 MiB          |
| JSON 중첩 깊이 (명제·도출 트리 포함)   | 512             |
| 선언 하나의 재계산 중 생성되는 명제 노드 수 | 10,000,000 |
| 번들의 선언 수                         | 100,000         |

- 제한을 넘으면 `E_LIMIT`으로 거부해야 한다. `E_LIMIT`은 증명이 틀렸다는 뜻이 아니다.
- 커널은 깊이 제한 검사를 재귀 처리보다 먼저 수행해야 하며, Python의 `RecursionError`나 메모리 부족으로 비정상 종료해서는 안 된다. JSON 파서의 중첩 한계도 같은 기준으로 다룬다.
- 깊이 기본값 512는 v0.1 커널이 재귀로 구현되어 Python 기본 재귀 한계(1000)와 표준 `json` 모듈의 중첩 한계 안에서 동작하도록 정한 값이다. 이보다 크게 설정하려면 디코딩과 결론 재계산을 반복(iterative) 방식으로 구현해야 한다.
- 명제는 해시 컨싱(hash-consing)으로 공유하므로, 명제 동등성 비교는 깊이와 무관하게 상수 시간이며 재귀를 쓰지 않는다. 노드 수 제한은 재계산 중 새로 만들어지는 명제 노드에 적용한다.

## 9. 허용 공리 정책

### 9.1. 형식

허용 공리 정책 `allowed_axioms`는 선언 이름을 선언 해시로 대응시키는 사상이다.

```python
{"classical.em": "sha256:e3dde0812143549271fc6753bfb9f64adce3be606a7b1eedfdd7feff7282c0dc"}
```

- 번들의 공리 선언 $d$는 `allowed_axioms[d.name] == hash(d)`일 때만 허용된다. 이름만 같고 명제가 다른 공리는 거부된다.
- 정책은 검증을 요청하는 쪽이 정하며, 인증서에 기록하지 않는다. 커널은 인증서 내용을 근거로 공리를 허용해서는 안 된다.

### 9.2. 표준 정책

커널은 다음 표준 정책 `STANDARD_AXIOMS`를 내장해야 한다.

| 이름           | 명제                        | 선언 해시 |
| -------------- | --------------------------- | --------- |
| `classical.em` | $P \lor (P \to \bot)$ (`["or", ["atom", "P"], ["imp", ["atom", "P"], ["false"]]]`) | `sha256:e3dde0812143549271fc6753bfb9f64adce3be606a7b1eedfdd7feff7282c0dc` |

이 해시는 `{"kind": "axiom", "name": "classical.em", "statement": …}`의 선언 해시이다. 따라서 [language-spec.md §10](language-spec.md#10-표준-theory-classical)의 `classical` Theory는 원자 이름 `P`로 이 명제를 선언해야 한다.

### 9.3. 언어 계층과의 연결

- `Theory.check(allowed_axioms=None)`의 이름 집합은 Elaborator가 정책 사상으로 바꾸어 커널에 전달한다. 표준 정책에 있는 이름은 표준 해시로, 그 밖의 이름은 사용자가 그 Theory에 선언한 공리의 해시로 대응시킨다.
- `axw verify`의 기본 정책은 `STANDARD_AXIOMS`이며, 추가 공리는 `--allow NAME=HASH`로 명시한다.

## 10. 결과와 오류

### 10.1. `KernelReport`

| 항목              | 의미                                                                       |
| ----------------- | -------------------------------------------------------------------------- |
| `bundle_ok`       | 1–5단계를 통과하면 `True`                                                  |
| `bundle_error`    | 1–5단계에서 실패한 경우의 오류                                             |
| `results`         | 선언별 결과 (배열 순서): 이름, 상태, 오류, 계산된 의존 공리                 |
| `ok`              | `bundle_ok`이고 모든 정리가 `VERIFIED`이면 `True`                          |

선언별 상태는 `VERIFIED`(정리 수락), `ACCEPTED`(허용된 공리), `REJECTED` 중 하나이다. 커널은 `UNPROVEN`을 보고하지 않는다. 미완성 증명은 커널에 도달하기 전에 언어 계층이 처리한다 ([language-spec.md §5.7](language-spec.md#57-검증-상태-전이)).

### 10.2. 오류 코드

오류는 코드, 선언 이름(있으면), 도출 안의 위치, 사람이 읽을 수 있는 설명을 포함해야 한다. 위치는 루트에서 해당 노드까지의 키·인덱스 경로(예: `proof.body.fn`)로 나타낸다.

| 코드                    | 의미                                                        | [specification.md §8](specification.md#8-v01-적합성-기준)의 실패 유형 |
| ----------------------- | ----------------------------------------------------------- | ---------------------------- |
| `E_FORMAT`              | JSON 제한 위반, 구조·키 집합 오류, 알 수 없는 태그          | 인증서 변조 등               |
| `E_VERSION`             | 지원하지 않는 형식 버전 또는 단편                           | —                            |
| `E_NAME`                | 이름 구문 위반, 예약어 사용                                 | 타입 오류                    |
| `E_FRAGMENT`            | L0 밖의 구성 요소 (`lam`, `forall` 등)                      | 단편 위반                    |
| `E_DUPLICATE_DECL`      | 선언 이름 중복                                              | —                            |
| `E_AXIOM_NOT_ALLOWED`   | 허용 정책에 없는 공리, 또는 이름은 같지만 해시가 다른 공리  | 미등록 공리                  |
| `E_HASH_MISMATCH`       | 선언·번들·참조 해시 불일치                                  | 인증서 변조                  |
| `E_HYP_UNKNOWN`         | 문맥에 없는 가정 이름 사용                                  | 잘못된 가정 참조, 해제되지 않은 가정 |
| `E_HYP_NOT_FRESH`       | 이미 문맥에 있는 가정 이름의 도입                           | 잘못된 가정 참조             |
| `E_RULE_MISMATCH`       | 전제의 명제 형태가 규칙과 맞지 않음                         | 규칙 전제 불일치             |
| `E_SUBST_DOMAIN`        | 치환 정의역이 선언 명제의 원자 집합에 포함되지 않음         | —                            |
| `E_UNKNOWN_DECL`        | 수락된 선언 중에 참조 대상이 없음 (미선언, 뒤 선언, 자기 자신, 거부된 정리, 종류 불일치) | 미검증 정리 참조, 순환 참조 |
| `E_CONCLUSION_MISMATCH` | 재계산한 결론과 선언 명제가 다름                            | 결론 불일치                  |
| `E_AXIOMS_MISMATCH`     | 기록된 의존 공리와 계산값이 다름                            | 인증서 변조                  |
| `E_LIMIT`               | 자원 제한 초과                                              | —                            |
| `E_INTERNAL`            | 커널 내부 오류 (버그)                                       | —                            |

- 원자 위치에 잘못된 값이 있는 경우(예: 원소 수가 틀린 `["and", A]`)는 디코딩 단계의 `E_FORMAT`이며, 이것이 logic-spec의 타입 오류에 해당한다.
- `E_INTERNAL`도 거부로 처리해야 한다. 커널은 내부 오류를 수락으로 바꾸어서는 안 된다.

## 11. 신뢰 기반과 모듈 경계

### 11.1. 커널 모듈

| 모듈 (README §6 구조)          | 역할                                           |
| ------------------------------ | ---------------------------------------------- |
| `axiomweave/kernel/certificate.py` | JSON 제한 검사, 디코딩, 정규화, 해시       |
| `axiomweave/kernel/rules.py`   | [8.4](#84-결론-재계산)의 규칙별 재계산         |
| `axiomweave/kernel/checker.py` | [8.2](#82-단계)–[8.3](#83-선언-검사)의 진입점과 환경 처리 |
| `axiomweave/kernel/axioms.py`  | 표준 허용 정책                                 |

- 커널 모듈은 Python 표준 라이브러리(`json`, `hashlib`, `re` 등)와 `axiomweave.kernel` 패키지 안의 모듈만 가져와야 한다. `axiomweave.core`, `language`, `tactics`, `backends`, `ai`를 가져와서는 안 된다. 이 경계는 테스트로 검사해야 한다.
- 커널은 명제와 도출을 자체 불변 표현(예: 튜플)으로 디코딩하여 다룬다. [specification.md §5.4](specification.md#54-신뢰-기반)의 "핵심 표현식 자료구조"는 이 커널 내부 표현을 뜻한다.
- 커널은 파일 시스템, 네트워크, 환경 변수, 플러그인, 하위 프로세스를 사용해서는 안 된다. 파일 읽기는 커널을 호출하는 쪽(CLI)이 담당한다.

### 11.2. 독립 재검증

- `axw verify <file.axwp>`는 사용자 Python 코드를 가져오지 않는 새 프로세스에서 파일을 읽어 `check_bundle`을 호출해야 한다. 이것이 [specification.md §8](specification.md#8-v01-적합성-기준)의 "별도 프로세스에서의 독립 재검증"이다.
- `axw verify`는 `KernelReport.ok`일 때만 종료 코드 0을 반환해야 한다.
- 같은 번들과 같은 정책에 대해 커널은 항상 같은 `KernelReport`를 내야 한다. 결과는 실행 시각, 해시 시드, 딕셔너리 순회 순서에 의존해서는 안 된다.

## 12. 예제

예제는 비규범적이다. 다음 번들은 정리 두 개를 담는다. 두 번째 정리는 첫 번째 정리를 $[P \mapsto P \land Q]$로 인스턴스화한다.

```json
{
  "format": "axwp",
  "format_version": 1,
  "spec_version": "0.1",
  "fragment": "L0",
  "kernel_version": "0.1.0.dev0",
  "theory": "demo.logic",
  "declarations": [
    {
      "kind": "theorem",
      "name": "demo.logic.imp_self",
      "statement": ["imp", ["atom", "P"], ["atom", "P"]],
      "proof": {
        "rule": "imp_i",
        "name": "h1",
        "hyp": ["atom", "P"],
        "body": {"rule": "hyp", "name": "h1"}
      },
      "hash": "sha256:0d5c615830ab989b8f25673ff0b33b01afbd6e186a52bfb6253992c56879fbe9",
      "axioms": []
    },
    {
      "kind": "theorem",
      "name": "demo.logic.imp_self_and",
      "statement": [
        "imp",
        ["and", ["atom", "P"], ["atom", "Q"]],
        ["and", ["atom", "P"], ["atom", "Q"]]
      ],
      "proof": {
        "rule": "thm",
        "name": "demo.logic.imp_self",
        "hash": "sha256:0d5c615830ab989b8f25673ff0b33b01afbd6e186a52bfb6253992c56879fbe9",
        "subst": {"P": ["and", ["atom", "P"], ["atom", "Q"]]}
      },
      "hash": "sha256:57a7ffb4af6dedcfbc201224221093f8873b54296c3c456e0c65fd145acf70d9",
      "axioms": []
    }
  ],
  "bundle_hash": "sha256:49f867f22ffb11d1ac92dca4555855fec4ada8bed9072ed91d9862d86f0cd5e1"
}
```

첫 번째 선언의 해시 입력 $\mathrm{canon}(d^{\circ})$는 다음 바이트열이다.

```text
{"kind":"theorem","name":"demo.logic.imp_self","proof":{"body":{"name":"h1","rule":"hyp"},"hyp":["atom","P"],"name":"h1","rule":"imp_i"},"statement":["imp",["atom","P"],["atom","P"]]}
```

변조 예:

| 변조                                                         | 결과                                        |
| ------------------------------------------------------------ | ------------------------------------------- |
| 첫 번째 `statement`를 `["imp", ["atom", "Q"], ["atom", "Q"]]`로 변경 | 선언 해시 불일치 (`E_HASH_MISMATCH`)   |
| 위 변경 후 `hash`와 `bundle_hash`도 다시 계산                | 첫 번째는 결론 불일치 (`E_CONCLUSION_MISMATCH`), 첫 번째가 환경에 들어가지 않으므로 두 번째는 `E_UNKNOWN_DECL` |
| `body`를 `{"rule": "hyp", "name": "h2"}`로 바꾸고 해시 재계산 | `E_HYP_UNKNOWN`                             |
| 두 선언의 순서를 바꾸고 `bundle_hash` 재계산                 | 앞에 온 `imp_self_and`는 `E_UNKNOWN_DECL`, 뒤에 온 `imp_self`는 `VERIFIED` |
| `axioms`를 `["classical.em"]`으로 변경                       | `E_AXIOMS_MISMATCH` (번들 해시도 다시 계산한 경우) |

## 13. 확장 시 유의 사항

이 절은 L1 이후 개정을 위한 비규범적 메모이다.

- L1에서 바인더를 도입하면 이름 표현(이름 기반 + 포획 회피 치환, de Bruijn 인덱스, 지역 이름 없는 표현)을 결정해야 한다. 어느 쪽이든 정규 JSON의 해시가 α-동치인 항에 대해 같도록 정할지 함께 결정해야 한다.
- 새 단편은 새 `fragment` 값과 새 태그로 추가하며, 기존 L0 번들은 형식 변경 없이 계속 검증 가능해야 한다.
- 정리별 인증서와 해시 기반 저장소(AxiomHub)는 선언 해시를 그대로 식별자로 사용할 수 있도록 설계되어 있다. 이 경우에도 검증은 자기완결 번들로 재구성한 뒤 수행하는 것을 권장한다.
- 큰 증명을 위한 구조 공유(DAG) 인코딩은 필요해질 때 `format_version`을 올려 도입한다.
